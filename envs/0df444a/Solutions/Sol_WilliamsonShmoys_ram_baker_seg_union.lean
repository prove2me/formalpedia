-- Prove2me | solution 1 for WilliamsonShmoys.ram_baker_seg_union
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T13:17:55.752812+00:00
-- url     : https://prove2.me/submissions/7c71e92a-8c9d-44bf-b8a4-9e33e627c5d9

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec
import Definitions.Def_WilliamsonShmoys_RAMSandboxOdd
import Theorems.Thm_WilliamsonShmoys_ram_union_instance_build
import Theorems.Thm_WilliamsonShmoys_union_input_decode

set_option autoImplicit false

namespace SG3B
open WilliamsonShmoys PlanarRAMInstruction

lemma step_exec (p : List PlanarRAMInstruction) (s : PlanarRAMState) (ins : PlanarRAMInstruction)
    (h : p[s.pc]? = some ins) : planarRAMStep p s = execInstr ins s := by
  unfold planarRAMStep
  rw [h]
  cases ins <;> rfl

lemma run_add (p : List PlanarRAMInstruction) (s : PlanarRAMState) (a b : ℕ) :
    planarRAMRun p s (a + b) = planarRAMRun p (planarRAMRun p s a) b := by
  unfold planarRAMRun
  rw [add_comm, Function.iterate_add_apply]

lemma run_succ (p : List PlanarRAMInstruction) (s : PlanarRAMState) (t : ℕ) :
    planarRAMRun p s (t + 1) = planarRAMRun p (planarRAMStep p s) t := by
  unfold planarRAMRun
  rw [Function.iterate_succ_apply]

lemma run_zero (p : List PlanarRAMInstruction) (s : PlanarRAMState) :
    planarRAMRun p s 0 = s := rfl

lemma step_at (p : List PlanarRAMInstruction) (b k : ℕ) {s : PlanarRAMState} (ins : PlanarRAMInstruction)
    (h1 : s.pc = b + k) (h2 : p[b + k]? = some ins) : planarRAMStep p s = execInstr ins s :=
  step_exec p s ins (by rw [h1]; exact h2)

lemma codeAt_sub (p : List PlanarRAMInstruction) (base off : ℕ) (code sub : List PlanarRAMInstruction)
    (hcode : CodeAt p base code) (hsub : ∀ i, i < sub.length → code[off + i]? = sub[i]?) :
    CodeAt p (base + off) sub := by
  intro i hi
  have h := hsub i hi
  have hlen : off + i < code.length := by
    by_contra hc
    push_neg at hc
    rw [List.getElem?_eq_none hc] at h
    exact absurd h.symm (by simp [List.getElem?_eq_getElem hi])
  rw [add_assoc, hcode (off + i) hlen, h]



lemma ex_const (d v pc : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) :
    execInstr (natConst d v) ⟨pc, M, R⟩ = ⟨pc + 1, Function.update M d v, R⟩ := rfl

lemma ex_add (d l r pc v : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) (h : M l + M r = v) :
    execInstr (natAdd d l r) ⟨pc, M, R⟩ = ⟨pc + 1, Function.update M d v, R⟩ := by
  rw [← h]; rfl

lemma ex_sub (d l r pc v : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) (h : M l - M r = v) :
    execInstr (natSub d l r) ⟨pc, M, R⟩ = ⟨pc + 1, Function.update M d v, R⟩ := by
  rw [← h]; rfl

lemma ex_load (d a pc v : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) (h : M (M a) = v) :
    execInstr (natLoad d a) ⟨pc, M, R⟩ = ⟨pc + 1, Function.update M d v, R⟩ := by
  rw [← h]; rfl

lemma ex_store (a src pc x v : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) (ha : M a = x) (hv : M src = v) :
    execInstr (natStore a src) ⟨pc, M, R⟩ = ⟨pc + 1, Function.update M x v, R⟩ := by
  rw [← ha, ← hv]; rfl

lemma ex_rzero (d pc : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) :
    execInstr (realZero d) ⟨pc, M, R⟩ = ⟨pc + 1, M, Function.update R d 0⟩ := rfl

lemma ex_rload (d a pc x : ℕ) (v : ℝ) (M : ℕ → ℕ) (R : ℕ → ℝ) (ha : M a = x) (h : R x = v) :
    execInstr (realLoad d a) ⟨pc, M, R⟩ = ⟨pc + 1, M, Function.update R d v⟩ := by
  rw [← h, ← ha]; rfl

lemma ex_rstore (a src pc x : ℕ) (v : ℝ) (M : ℕ → ℕ) (R : ℕ → ℝ) (ha : M a = x) (hv : R src = v) :
    execInstr (realStore a src) ⟨pc, M, R⟩ = ⟨pc + 1, M, Function.update R x v⟩ := by
  rw [← ha, ← hv]; rfl

lemma ex_brt (l r y n pc : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) (h : M l ≤ M r) :
    execInstr (natBranch l r y n) ⟨pc, M, R⟩ = ⟨y, M, R⟩ := by
  simp [execInstr, h]

lemma ex_brf (l r y n pc : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) (h : ¬ M l ≤ M r) :
    execInstr (natBranch l r y n) ⟨pc, M, R⟩ = ⟨n, M, R⟩ := by
  simp [execInstr, h]

lemma ex_jump (j pc : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) :
    execInstr (jump j) ⟨pc, M, R⟩ = ⟨j, M, R⟩ := rfl

lemma step_at' (p : List PlanarRAMInstruction) (b k pc : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ)
    (ins : PlanarRAMInstruction) (h1 : pc = b + k) (h2 : p[b + k]? = some ins) :
    planarRAMStep p ⟨pc, M, R⟩ = execInstr ins ⟨pc, M, R⟩ :=
  step_exec p _ ins (by simp only; rw [h1]; exact h2)

lemma ex_radd (d l r pc : ℕ) (v : ℝ) (M : ℕ → ℕ) (R : ℕ → ℝ) (h : R l + R r = v) :
    execInstr (realAdd d l r) ⟨pc, M, R⟩ = ⟨pc + 1, M, Function.update R d v⟩ := by
  rw [← h]; rfl

lemma ex_rbrt (l r y n pc : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) (h : R l ≤ R r) :
    execInstr (realBranch l r y n) ⟨pc, M, R⟩ = ⟨y, M, R⟩ := by
  simp [execInstr, h]

lemma ex_rbrf (l r y n pc : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) (h : ¬ R l ≤ R r) :
    execInstr (realBranch l r y n) ⟨pc, M, R⟩ = ⟨n, M, R⟩ := by
  simp [execInstr, h]


set_option maxHeartbeats 4000000 in
lemma g3_loop (p : List PlanarRAMInstruction) (hg3 : CodeAt p 261 [natConst 0 0, natConst 4 0, natConst 6 0, natConst 8 1, natBranch 32 6 (261 + 8) (261 + 5), natAdd 4 4 32, natAdd 6 6 8, jump (261 + 4), natAdd 28 4 4, natAdd 28 28 28, natAdd 28 28 28, natAdd 28 28 28, natAdd 6 32 32, natAdd 6 6 6, natAdd 6 6 6, natAdd 6 6 6, natAdd 28 28 6, natConst 6 48, natAdd 28 28 6, natAdd 40 32 0, natAdd 42 28 0, natConst 2 1]) (K : ℕ) :
    ∀ (r i acc : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), i + r = K →
      M 32 = K → M 8 = 1 → M 6 = i → M 4 = acc →
      ∃ τ, τ ≤ 4 * r + 1 ∧ (planarRAMRun p ⟨261 + 4, M, R⟩ τ).pc = 261 + 8 ∧
        (planarRAMRun p ⟨261 + 4, M, R⟩ τ).natMem 4 = acc + r * K ∧
        (∀ a, a ≠ 6 → a ≠ 4 → (planarRAMRun p ⟨261 + 4, M, R⟩ τ).natMem a = M a) ∧
        (planarRAMRun p ⟨261 + 4, M, R⟩ τ).realMem = R := by
  have g0 : p[261 + 0]? = some (natConst 0 0) := by simpa using hg3 0 (by simp)
  have g1 : p[261 + 1]? = some (natConst 4 0) := by simpa using hg3 1 (by simp)
  have g2 : p[261 + 2]? = some (natConst 6 0) := by simpa using hg3 2 (by simp)
  have g3 : p[261 + 3]? = some (natConst 8 1) := by simpa using hg3 3 (by simp)
  have g4 : p[261 + 4]? = some (natBranch 32 6 (261 + 8) (261 + 5)) := by simpa using hg3 4 (by simp)
  have g5 : p[261 + 5]? = some (natAdd 4 4 32) := by simpa using hg3 5 (by simp)
  have g6 : p[261 + 6]? = some (natAdd 6 6 8) := by simpa using hg3 6 (by simp)
  have g7 : p[261 + 7]? = some (jump (261 + 4)) := by simpa using hg3 7 (by simp)
  have g8 : p[261 + 8]? = some (natAdd 28 4 4) := by simpa using hg3 8 (by simp)
  have g9 : p[261 + 9]? = some (natAdd 28 28 28) := by simpa using hg3 9 (by simp)
  have g10 : p[261 + 10]? = some (natAdd 28 28 28) := by simpa using hg3 10 (by simp)
  have g11 : p[261 + 11]? = some (natAdd 28 28 28) := by simpa using hg3 11 (by simp)
  have g12 : p[261 + 12]? = some (natAdd 6 32 32) := by simpa using hg3 12 (by simp)
  have g13 : p[261 + 13]? = some (natAdd 6 6 6) := by simpa using hg3 13 (by simp)
  have g14 : p[261 + 14]? = some (natAdd 6 6 6) := by simpa using hg3 14 (by simp)
  have g15 : p[261 + 15]? = some (natAdd 6 6 6) := by simpa using hg3 15 (by simp)
  have g16 : p[261 + 16]? = some (natAdd 28 28 6) := by simpa using hg3 16 (by simp)
  have g17 : p[261 + 17]? = some (natConst 6 48) := by simpa using hg3 17 (by simp)
  have g18 : p[261 + 18]? = some (natAdd 28 28 6) := by simpa using hg3 18 (by simp)
  have g19 : p[261 + 19]? = some (natAdd 40 32 0) := by simpa using hg3 19 (by simp)
  have g20 : p[261 + 20]? = some (natAdd 42 28 0) := by simpa using hg3 20 (by simp)
  have g21 : p[261 + 21]? = some (natConst 2 1) := by simpa using hg3 21 (by simp)
  intro r
  induction r with
  | zero =>
    intro i acc M R hi hL h8 h6 hA
    refine ⟨1, by omega, ?_⟩
    rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_at p 261 4 _ rfl g4, run_zero]
    simp only [execInstr, show M 32 ≤ M 6 by omega, if_true]
    exact ⟨trivial, by simp [hA], fun a _ _ => trivial, trivial⟩
  | succ r ih =>
    intro i acc M R hi hL h8 h6 hA
    have hlt : ¬ M 32 ≤ M 6 := by omega
    obtain ⟨τ2, hτ2, r1, rA, rfr, rr⟩ := ih (i + 1) (acc + K)
      (Function.update (Function.update M 4 (acc + K)) 6 (i + 1)) R (by omega)
      (by simp [Function.update_apply, hL]) (by simp [Function.update_apply, h8])
      (by simp) (by simp [Function.update_apply])
    refine ⟨4 + τ2, by omega, ?_⟩
    have e4 : planarRAMRun p ⟨261 + 4, M, R⟩ 4 =
        ⟨261 + 4, Function.update (Function.update M 4 (acc + K)) 6 (i + 1), R⟩ := by
      rw [show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 from rfl, run_succ, step_at' p 261 4 _ _ _ _ (by omega) g4,
        ex_brf _ _ _ _ _ _ _ hlt, run_succ, step_at' p 261 5 _ _ _ _ (by omega) g5,
        ex_add _ _ _ _ _ _ _ (by rw [hA, hL]), run_succ, step_at' p 261 6 _ _ _ _ (by omega) g6,
        ex_add _ _ _ _ _ _ _ (by simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte, h6, h8]; rfl),
        run_succ, step_at' p 261 7 _ _ _ _ (by omega) g7, ex_jump, run_zero]
    rw [run_add, e4]
    refine ⟨r1, by rw [rA]; ring, fun a a6 aA => ?_, rr⟩
    rw [rfr a a6 aA, Function.update_of_ne a6, Function.update_of_ne aA]

open Classical in
set_option maxHeartbeats 16000000 in
lemma seg3b (p : List PlanarRAMInstruction)
    (hc : CodeAt p 207 [natConst 0 0, natConst 2 1, natConst 4 2, natAdd 26 32 32, natAdd 30 28 26, natConst 8 0, natConst 6 0, natBranch 34 6 (207 + 11) (207 + 8), natAdd 8 8 32, natAdd 6 6 2, jump (207 + 7), natAdd 10 8 8, natSub 24 10 26, natConst 10 1, natStore 10 8, natAdd 8 34 34, natAdd 8 8 34, natConst 10 3, natStore 10 8, natConst 6 0, natConst 18 5, natConst 22 1, natBranch 34 6 (207 + 54) (207 + 23), natAdd 12 28 0, natConst 20 32, natConst 16 36, natBranch 30 12 (207 + 51) (207 + 27), natLoad 8 12, natBranch 8 6 (207 + 29) (207 + 30), natBranch 6 8 (207 + 44) (207 + 30), realLoad 0 20, realStore 22 0, natAdd 14 28 0, natBranch 30 14 (207 + 46) (207 + 34), natLoad 10 14, natBranch 10 6 (207 + 36) (207 + 37), natBranch 6 10 (207 + 40) (207 + 37), natLoad 10 16, natBranch 2 10 (207 + 39) (207 + 40), natStore 18 2, natAdd 14 14 4, natAdd 16 16 4, natAdd 18 18 4, jump (207 + 33), natAdd 16 16 26, natAdd 18 18 26, natAdd 18 18 24, natAdd 12 12 4, natAdd 20 20 4, natAdd 22 22 4, jump (207 + 26), natAdd 18 18 26, natAdd 6 6 2, jump (207 + 22)])
    (hg3 : CodeAt p 261 [natConst 0 0, natConst 4 0, natConst 6 0, natConst 8 1, natBranch 32 6 (261 + 8) (261 + 5), natAdd 4 4 32, natAdd 6 6 8, jump (261 + 4), natAdd 28 4 4, natAdd 28 28 28, natAdd 28 28 28, natAdd 28 28 28, natAdd 6 32 32, natAdd 6 6 6, natAdd 6 6 6, natAdd 6 6 6, natAdd 28 28 6, natConst 6 48, natAdd 28 28 6, natAdd 40 32 0, natAdd 42 28 0, natConst 2 1])
    (n k : ℕ) (hk : 0 < k) (M : ℕ → ℕ) (R : ℕ → ℝ)
    (h32 : M 32 = n) (h34 : M 34 = k) (h28 : M 28 = (16 * (n * n) + 16 * n + 48))
    (hodd : ∀ a, a % 2 = 1 → M a = 0) (hRodd : ∀ a, a % 2 = 1 → R a = 0) :
    ∃ τ, τ ≤ ((11 * n + 20) * n + 12) * k + 4 * n + 50 ∧ (planarRAMRun p ⟨207, M, R⟩ τ).pc = 283 ∧
      SandboxOddRel 2 (planarRAMInput (k * n) (3 * k) (fun x y : Fin (k * n) => decide (x.val / n = y.val / n ∧ M ((16 * (n * n) + 16 * n + 48) + 2 * (x.val % n)) ≠ x.val / n ∧ M ((16 * (n * n) + 16 * n + 48) + 2 * (y.val % n)) ≠ x.val / n ∧ 1 ≤ M (36 + 2 * (x.val % n) * n + 2 * (y.val % n)))) (fun x : Fin (k * n) => if M ((16 * (n * n) + 16 * n + 48) + 2 * (x.val % n)) ≠ x.val / n then R (32 + 2 * (x.val % n)) else 0)) (planarRAMRun p ⟨207, M, R⟩ τ) ∧
      (planarRAMRun p ⟨207, M, R⟩ τ).natMem 32 = n ∧ (planarRAMRun p ⟨207, M, R⟩ τ).natMem 34 = k ∧ (planarRAMRun p ⟨207, M, R⟩ τ).natMem 28 = (16 * (n * n) + 16 * n + 48) ∧
      (planarRAMRun p ⟨207, M, R⟩ τ).natMem 40 = n ∧ (planarRAMRun p ⟨207, M, R⟩ τ).natMem 42 = (16 * (n * n) + 16 * n + 48) ∧
      (∀ a, a % 2 = 0 → 44 ≤ a → (planarRAMRun p ⟨207, M, R⟩ τ).natMem a = M a) ∧
      (∀ a, a % 2 = 0 → a ≠ 0 → (planarRAMRun p ⟨207, M, R⟩ τ).realMem a = R a) := by
  set LVB := (16 * (n * n) + 16 * n + 48) with hLVB
  have hLe : LVB % 2 = 0 := by rw [hLVB]; omega
  have hL36 : 36 + 2 * n * n ≤ LVB := by rw [hLVB]; nlinarith
  obtain ⟨τb, hτb, u1, u1n, u3, uT, uR, uev, uodd, uRfr⟩ :=
    ram_union_instance_build p 207 hc n k LVB hk hLe hL36 M R h32 h34 h28
  set S1 := planarRAMRun p ⟨207, M, R⟩ τb with hS1
  obtain ⟨pc1, M1, R1⟩ := S1
  simp only at u1 u1n u3 uT uR uev uodd uRfr
  have e1 : pc1 = 261 := by omega
  subst e1
  have g0 : p[261 + 0]? = some (natConst 0 0) := by simpa using hg3 0 (by simp)
  have g1 : p[261 + 1]? = some (natConst 4 0) := by simpa using hg3 1 (by simp)
  have g2 : p[261 + 2]? = some (natConst 6 0) := by simpa using hg3 2 (by simp)
  have g3 : p[261 + 3]? = some (natConst 8 1) := by simpa using hg3 3 (by simp)
  have g4 : p[261 + 4]? = some (natBranch 32 6 (261 + 8) (261 + 5)) := by simpa using hg3 4 (by simp)
  have g5 : p[261 + 5]? = some (natAdd 4 4 32) := by simpa using hg3 5 (by simp)
  have g6 : p[261 + 6]? = some (natAdd 6 6 8) := by simpa using hg3 6 (by simp)
  have g7 : p[261 + 7]? = some (jump (261 + 4)) := by simpa using hg3 7 (by simp)
  have g8 : p[261 + 8]? = some (natAdd 28 4 4) := by simpa using hg3 8 (by simp)
  have g9 : p[261 + 9]? = some (natAdd 28 28 28) := by simpa using hg3 9 (by simp)
  have g10 : p[261 + 10]? = some (natAdd 28 28 28) := by simpa using hg3 10 (by simp)
  have g11 : p[261 + 11]? = some (natAdd 28 28 28) := by simpa using hg3 11 (by simp)
  have g12 : p[261 + 12]? = some (natAdd 6 32 32) := by simpa using hg3 12 (by simp)
  have g13 : p[261 + 13]? = some (natAdd 6 6 6) := by simpa using hg3 13 (by simp)
  have g14 : p[261 + 14]? = some (natAdd 6 6 6) := by simpa using hg3 14 (by simp)
  have g15 : p[261 + 15]? = some (natAdd 6 6 6) := by simpa using hg3 15 (by simp)
  have g16 : p[261 + 16]? = some (natAdd 28 28 6) := by simpa using hg3 16 (by simp)
  have g17 : p[261 + 17]? = some (natConst 6 48) := by simpa using hg3 17 (by simp)
  have g18 : p[261 + 18]? = some (natAdd 28 28 6) := by simpa using hg3 18 (by simp)
  have g19 : p[261 + 19]? = some (natAdd 40 32 0) := by simpa using hg3 19 (by simp)
  have g20 : p[261 + 20]? = some (natAdd 42 28 0) := by simpa using hg3 20 (by simp)
  have g21 : p[261 + 21]? = some (natConst 2 1) := by simpa using hg3 21 (by simp)
  have sA : (planarRAMRun p ⟨261, M1, R1⟩ 4).pc = 261 + 4 ∧ (planarRAMRun p ⟨261, M1, R1⟩ 4).natMem 0 = 0 ∧ (planarRAMRun p ⟨261, M1, R1⟩ 4).natMem 4 = 0 ∧ (planarRAMRun p ⟨261, M1, R1⟩ 4).natMem 6 = 0 ∧
      (planarRAMRun p ⟨261, M1, R1⟩ 4).natMem 8 = 1 ∧ (∀ a, a ≠ 0 → a ≠ 4 → a ≠ 6 → a ≠ 8 → (planarRAMRun p ⟨261, M1, R1⟩ 4).natMem a = M1 a) ∧ (planarRAMRun p ⟨261, M1, R1⟩ 4).realMem = R1 := by
    rw [show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 from rfl]
    rw [run_succ, step_at' p 261 0 _ _ _ _ (by omega) g0, ex_const, run_succ, step_at' p 261 1 _ _ _ _ (by omega) g1,
      ex_const, run_succ, step_at' p 261 2 _ _ _ _ (by omega) g2, ex_const, run_succ,
      step_at' p 261 3 _ _ _ _ (by omega) g3, ex_const, run_zero]
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
    all_goals first
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, u1n]; done)
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, u1n] <;> omega)
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, u1n]; ring1)
      | (intro a a0 a4 a6 a8; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, a0, a4, a6, a8])
  obtain ⟨a1, a0, a4, a6, a8, afr, ar⟩ := sA
  set S2 := planarRAMRun p ⟨261, M1, R1⟩ 4 with hS2
  obtain ⟨pc2, M2, R2⟩ := S2
  simp only at a1 a0 a4 a6 a8 afr ar
  subst a1; subst R2
  have m32 : M2 32 = n := by rw [afr 32 (by omega) (by omega) (by omega) (by omega), uev 32 (by omega) (by omega), h32]
  obtain ⟨τl, hτl, l1, l4, lfr, lr⟩ := g3_loop p hg3 n n 0 0 M2 R1 (by omega) m32 a8 a6 a4
  set S3 := planarRAMRun p ⟨261 + 4, M2, R1⟩ τl with hS3
  obtain ⟨pc3, M3, R3⟩ := S3
  simp only at l1 l4 lfr lr
  subst l1; subst R3
  have g4' : M3 4 = n * n := by rw [l4]; ring
  have m32' : M3 32 = n := by rw [lfr 32 (by omega) (by omega), m32]
  have m0 : M3 0 = 0 := by rw [lfr 0 (by omega) (by omega), a0]
  have sB : (planarRAMRun p ⟨261 + 8, M3, R1⟩ 14).pc = 283 ∧ (planarRAMRun p ⟨261 + 8, M3, R1⟩ 14).natMem 28 = LVB ∧
      (planarRAMRun p ⟨261 + 8, M3, R1⟩ 14).natMem 40 = n ∧ (planarRAMRun p ⟨261 + 8, M3, R1⟩ 14).natMem 42 = LVB ∧
      (planarRAMRun p ⟨261 + 8, M3, R1⟩ 14).natMem 2 = 1 ∧
      (∀ a, a ≠ 28 → a ≠ 6 → a ≠ 40 → a ≠ 42 → a ≠ 2 → (planarRAMRun p ⟨261 + 8, M3, R1⟩ 14).natMem a = M3 a) ∧ (planarRAMRun p ⟨261 + 8, M3, R1⟩ 14).realMem = R1 := by
    rw [show (14 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
    rw [run_succ, step_at' p 261 8 _ _ _ _ (by omega) g8, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g4', m32', m0] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p 261 9 _ _ _ _ (by omega) g9, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g4', m32', m0] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p 261 10 _ _ _ _ (by omega) g10, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g4', m32', m0] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p 261 11 _ _ _ _ (by omega) g11, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g4', m32', m0] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p 261 12 _ _ _ _ (by omega) g12, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g4', m32', m0] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p 261 13 _ _ _ _ (by omega) g13, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g4', m32', m0] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p 261 14 _ _ _ _ (by omega) g14, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g4', m32', m0] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p 261 15 _ _ _ _ (by omega) g15, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g4', m32', m0] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p 261 16 _ _ _ _ (by omega) g16, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g4', m32', m0] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p 261 17 _ _ _ _ (by omega) g17, ex_const]
    rw [run_succ, step_at' p 261 18 _ _ _ _ (by omega) g18, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g4', m32', m0] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p 261 19 _ _ _ _ (by omega) g19, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g4', m32', m0] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p 261 20 _ _ _ _ (by omega) g20, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g4', m32', m0] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p 261 21 _ _ _ _ (by omega) g21, ex_const]
    rw [run_zero]
    try rfl
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
    all_goals first
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, g4', m32', m0]; done)
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, g4', m32', m0] <;> omega)
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, g4', m32', m0]; ring1)
      | (intro a a28 a6 a40 a42 a2; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, a28, a6, a40, a42, a2])
  obtain ⟨b1, b28, b40, b42, b2, bfr, br⟩ := sB
  set S4 := planarRAMRun p ⟨261 + 8, M3, R1⟩ 14 with hS4
  obtain ⟨pc4, M4, R4⟩ := S4
  simp only at b1 b28 b40 b42 b2 bfr br
  subst b1; subst R4
  have hodd4 : ∀ a, a % 2 = 1 → M4 a = M1 a := fun a ha => by
    rw [bfr a (by omega) (by omega) (by omega) (by omega) (by omega), lfr a (by omega) (by omega),
      afr a (by omega) (by omega) (by omega) (by omega)]
  have hT : ∀ c v w, c < k → v < n → w < n → M4 (5 + 2 * ((c * n + v) * (k * n) + (c * n + w))) =
      if M (LVB + 2 * v) ≠ c ∧ M (LVB + 2 * w) ≠ c ∧ 1 ≤ M (36 + 2 * v * n + 2 * w) then 1 else 0 := by
    intro c v w hc hv hw
    rw [hodd4 _ (by omega), uT c v w hc hv hw, hodd (5 + 2 * ((c * n + v) * (k * n) + (c * n + w))) (by omega)]
  have hO : ∀ a, a % 2 = 1 → a ≠ 1 → a ≠ 3 →
      (∀ c v w, c < k → v < n → w < n → a ≠ 5 + 2 * ((c * n + v) * (k * n) + (c * n + w))) → M4 a = 0 := by
    intro a ha a1 a3 aT
    rw [hodd4 a ha, uodd a ha a1 a3 aT, hodd a ha]
  have hR : ∀ c v, c < k → v < n → R1 (2 * (c * n + v) + 1) = if M (LVB + 2 * v) ≠ c then R (32 + 2 * v) else 0 := by
    intro c v hc hv
    rw [uR c v hc hv, hRodd (2 * (c * n + v) + 1) (by omega)]
  have hRO : ∀ a, a % 2 = 1 → (∀ c v, c < k → v < n → a ≠ 2 * (c * n + v) + 1) → R1 a = 0 := by
    intro a ha aD
    rw [uRfr a (by omega) aD, hRodd a ha]
  have hrel : (∀ a, M4 (2 * a + 1) = (planarRAMInput (k * n) (3 * k) (fun x y : Fin (k * n) => decide (x.val / n = y.val / n ∧ M ((16 * (n * n) + 16 * n + 48) + 2 * (x.val % n)) ≠ x.val / n ∧ M ((16 * (n * n) + 16 * n + 48) + 2 * (y.val % n)) ≠ x.val / n ∧ 1 ≤ M (36 + 2 * (x.val % n) * n + 2 * (y.val % n)))) (fun x : Fin (k * n) => if M ((16 * (n * n) + 16 * n + 48) + 2 * (x.val % n)) ≠ x.val / n then R (32 + 2 * (x.val % n)) else 0)).natMem a) ∧
      (∀ a, R1 (2 * a + 1) = (planarRAMInput (k * n) (3 * k) (fun x y : Fin (k * n) => decide (x.val / n = y.val / n ∧ M ((16 * (n * n) + 16 * n + 48) + 2 * (x.val % n)) ≠ x.val / n ∧ M ((16 * (n * n) + 16 * n + 48) + 2 * (y.val % n)) ≠ x.val / n ∧ 1 ≤ M (36 + 2 * (x.val % n) * n + 2 * (y.val % n)))) (fun x : Fin (k * n) => if M ((16 * (n * n) + 16 * n + 48) + 2 * (x.val % n)) ≠ x.val / n then R (32 + 2 * (x.val % n)) else 0)).realMem a) := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst hn0
      constructor
      · intro a
        simp only [planarRAMInput, Nat.mul_zero]
        by_cases a0 : a = 0
        · subst a0; simp only [if_pos rfl]; rw [hodd4 1 (by omega), u1n]; simp
        by_cases a1 : a = 1
        · subst a1; simp only [if_neg (show (1 : ℕ) ≠ 0 by omega), if_pos rfl]
          rw [hodd4 3 (by omega), u3]; simp
        rw [if_neg a0, if_neg a1, dif_neg (by simp)]
        exact hO _ (by omega) (by omega) (by omega) (fun c v w _ hv _ => by omega)
      · intro a
        simp only [planarRAMInput, Nat.mul_zero, dif_neg (Nat.not_lt_zero a)]
        exact hRO _ (by omega) (fun c v _ hv => by omega)
    · exact WilliamsonShmoys.union_input_decode n k hn (fun i => M (LVB + 2 * i))
        (fun v w => M (36 + 2 * v * n + 2 * w)) (fun v => R (32 + 2 * v)) M4 R1
        (by rw [hodd4 1 (by omega), u1n]) (by rw [hodd4 3 (by omega), u3]) hT hO hR hRO
  refine ⟨τb + 4 + τl + 14, by omega, ?_⟩
  rw [run_add, run_add, run_add, ← hS1, ← hS2, ← hS3, ← hS4]
  refine ⟨rfl, ⟨b2, hrel.1, hrel.2⟩, ?_, ?_, b28, b40, b42, fun a ha h44 => ?_, fun a ha a0 => ?_⟩
  · change M4 32 = n
    rw [bfr 32 (by omega) (by omega) (by omega) (by omega) (by omega), m32']
  · change M4 34 = k
    rw [bfr 34 (by omega) (by omega) (by omega) (by omega) (by omega), lfr 34 (by omega) (by omega),
      afr 34 (by omega) (by omega) (by omega) (by omega), uev 34 (by omega) (by omega), h34]
  · change M4 a = M a
    rw [bfr a (by omega) (by omega) (by omega) (by omega) (by omega), lfr a (by omega) (by omega),
      afr a (by omega) (by omega) (by omega) (by omega), uev a ha (by omega)]
  · change R1 a = R a
    exact uRfr a a0 (fun c v _ _ h => by omega)

end SG3B

open WilliamsonShmoys PlanarRAMInstruction
open Classical in
theorem solution (p : List PlanarRAMInstruction)
    (hc : CodeAt p 207 [natConst 0 0, natConst 2 1, natConst 4 2, natAdd 26 32 32, natAdd 30 28 26, natConst 8 0, natConst 6 0, natBranch 34 6 (207 + 11) (207 + 8), natAdd 8 8 32, natAdd 6 6 2, jump (207 + 7), natAdd 10 8 8, natSub 24 10 26, natConst 10 1, natStore 10 8, natAdd 8 34 34, natAdd 8 8 34, natConst 10 3, natStore 10 8, natConst 6 0, natConst 18 5, natConst 22 1, natBranch 34 6 (207 + 54) (207 + 23), natAdd 12 28 0, natConst 20 32, natConst 16 36, natBranch 30 12 (207 + 51) (207 + 27), natLoad 8 12, natBranch 8 6 (207 + 29) (207 + 30), natBranch 6 8 (207 + 44) (207 + 30), realLoad 0 20, realStore 22 0, natAdd 14 28 0, natBranch 30 14 (207 + 46) (207 + 34), natLoad 10 14, natBranch 10 6 (207 + 36) (207 + 37), natBranch 6 10 (207 + 40) (207 + 37), natLoad 10 16, natBranch 2 10 (207 + 39) (207 + 40), natStore 18 2, natAdd 14 14 4, natAdd 16 16 4, natAdd 18 18 4, jump (207 + 33), natAdd 16 16 26, natAdd 18 18 26, natAdd 18 18 24, natAdd 12 12 4, natAdd 20 20 4, natAdd 22 22 4, jump (207 + 26), natAdd 18 18 26, natAdd 6 6 2, jump (207 + 22)])
    (hg3 : CodeAt p 261 [natConst 0 0, natConst 4 0, natConst 6 0, natConst 8 1, natBranch 32 6 (261 + 8) (261 + 5), natAdd 4 4 32, natAdd 6 6 8, jump (261 + 4), natAdd 28 4 4, natAdd 28 28 28, natAdd 28 28 28, natAdd 28 28 28, natAdd 6 32 32, natAdd 6 6 6, natAdd 6 6 6, natAdd 6 6 6, natAdd 28 28 6, natConst 6 48, natAdd 28 28 6, natAdd 40 32 0, natAdd 42 28 0, natConst 2 1])
    (n k : ℕ) (hk : 0 < k) (M : ℕ → ℕ) (R : ℕ → ℝ)
    (h32 : M 32 = n) (h34 : M 34 = k) (h28 : M 28 = (16 * (n * n) + 16 * n + 48))
    (hodd : ∀ a, a % 2 = 1 → M a = 0) (hRodd : ∀ a, a % 2 = 1 → R a = 0) :
    ∃ τ, τ ≤ ((11 * n + 20) * n + 12) * k + 4 * n + 50 ∧ (planarRAMRun p ⟨207, M, R⟩ τ).pc = 283 ∧
      SandboxOddRel 2 (planarRAMInput (k * n) (3 * k) (fun x y : Fin (k * n) => decide (x.val / n = y.val / n ∧ M ((16 * (n * n) + 16 * n + 48) + 2 * (x.val % n)) ≠ x.val / n ∧ M ((16 * (n * n) + 16 * n + 48) + 2 * (y.val % n)) ≠ x.val / n ∧ 1 ≤ M (36 + 2 * (x.val % n) * n + 2 * (y.val % n)))) (fun x : Fin (k * n) => if M ((16 * (n * n) + 16 * n + 48) + 2 * (x.val % n)) ≠ x.val / n then R (32 + 2 * (x.val % n)) else 0)) (planarRAMRun p ⟨207, M, R⟩ τ) ∧
      (planarRAMRun p ⟨207, M, R⟩ τ).natMem 32 = n ∧ (planarRAMRun p ⟨207, M, R⟩ τ).natMem 34 = k ∧ (planarRAMRun p ⟨207, M, R⟩ τ).natMem 28 = (16 * (n * n) + 16 * n + 48) ∧
      (planarRAMRun p ⟨207, M, R⟩ τ).natMem 40 = n ∧ (planarRAMRun p ⟨207, M, R⟩ τ).natMem 42 = (16 * (n * n) + 16 * n + 48) ∧
      (∀ a, a % 2 = 0 → 44 ≤ a → (planarRAMRun p ⟨207, M, R⟩ τ).natMem a = M a) ∧
      (∀ a, a % 2 = 0 → a ≠ 0 → (planarRAMRun p ⟨207, M, R⟩ τ).realMem a = R a) :=
  SG3B.seg3b p hc hg3 n k hk M R h32 h34 h28 hodd hRodd
