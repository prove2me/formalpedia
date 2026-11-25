-- Prove2me | solution 2 for WilliamsonShmoys.ram_baker_seg_registers
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T13:27:45.848717+00:00
-- url     : https://prove2.me/submissions/a71745cd-5ea6-47c3-9ae6-ac21957d4d9a

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false

namespace SG2
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

section
variable (p : List PlanarRAMInstruction) (b : ℕ)
  (hcode : CodeAt p b
    [natAdd 13 0 12,
      natAdd 20 0 0,
      natConst 19 2,
      natAdd 31 0 11,
      natConst 1 0,
      natConst 3 0,
      natBranch 0 3 (b + 10) (b + 7),
      natAdd 1 1 0,
      natAdd 3 3 11,
      jump (b + 6),
      natAdd 28 1 1,
      natAdd 28 28 28,
      natAdd 28 28 28,
      natAdd 28 28 28,
      natAdd 5 20 20,
      natAdd 5 5 5,
      natAdd 5 5 5,
      natAdd 28 28 5,
      natConst 5 48,
      natAdd 28 28 5,
      natConst 2 36,
      natAdd 3 20 10,
      natConst 4 0,
      natBranch 0 4 (b + 28) (b + 24),
      natStore 2 12,
      natAdd 2 2 3,
      natAdd 4 4 11,
      jump (b + 23)])
include hcode

set_option maxHeartbeats 4000000 in
lemma sqq_loop (K : ℕ) :
    ∀ (r i acc : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), i + r = K →
      M 0 = K → M 11 = 1 → M 3 = i → M 1 = acc →
      ∃ τ, τ ≤ 4 * r + 1 ∧ (planarRAMRun p ⟨b + 6, M, R⟩ τ).pc = b + 10 ∧
        (planarRAMRun p ⟨b + 6, M, R⟩ τ).natMem 1 = acc + r * K ∧
        (∀ a, a ≠ 3 → a ≠ 1 → (planarRAMRun p ⟨b + 6, M, R⟩ τ).natMem a = M a) ∧
        (planarRAMRun p ⟨b + 6, M, R⟩ τ).realMem = R := by
  have c0 : p[b + 0]? = some (natAdd 13 0 12) := by simpa using hcode 0 (by simp)
  have c1 : p[b + 1]? = some (natAdd 20 0 0) := by simpa using hcode 1 (by simp)
  have c2 : p[b + 2]? = some (natConst 19 2) := by simpa using hcode 2 (by simp)
  have c3 : p[b + 3]? = some (natAdd 31 0 11) := by simpa using hcode 3 (by simp)
  have c4 : p[b + 4]? = some (natConst 1 0) := by simpa using hcode 4 (by simp)
  have c5 : p[b + 5]? = some (natConst 3 0) := by simpa using hcode 5 (by simp)
  have c6 : p[b + 6]? = some (natBranch 0 3 (b + 10) (b + 7)) := by simpa using hcode 6 (by simp)
  have c7 : p[b + 7]? = some (natAdd 1 1 0) := by simpa using hcode 7 (by simp)
  have c8 : p[b + 8]? = some (natAdd 3 3 11) := by simpa using hcode 8 (by simp)
  have c9 : p[b + 9]? = some (jump (b + 6)) := by simpa using hcode 9 (by simp)
  have c10 : p[b + 10]? = some (natAdd 28 1 1) := by simpa using hcode 10 (by simp)
  have c11 : p[b + 11]? = some (natAdd 28 28 28) := by simpa using hcode 11 (by simp)
  have c12 : p[b + 12]? = some (natAdd 28 28 28) := by simpa using hcode 12 (by simp)
  have c13 : p[b + 13]? = some (natAdd 28 28 28) := by simpa using hcode 13 (by simp)
  have c14 : p[b + 14]? = some (natAdd 5 20 20) := by simpa using hcode 14 (by simp)
  have c15 : p[b + 15]? = some (natAdd 5 5 5) := by simpa using hcode 15 (by simp)
  have c16 : p[b + 16]? = some (natAdd 5 5 5) := by simpa using hcode 16 (by simp)
  have c17 : p[b + 17]? = some (natAdd 28 28 5) := by simpa using hcode 17 (by simp)
  have c18 : p[b + 18]? = some (natConst 5 48) := by simpa using hcode 18 (by simp)
  have c19 : p[b + 19]? = some (natAdd 28 28 5) := by simpa using hcode 19 (by simp)
  have c20 : p[b + 20]? = some (natConst 2 36) := by simpa using hcode 20 (by simp)
  have c21 : p[b + 21]? = some (natAdd 3 20 10) := by simpa using hcode 21 (by simp)
  have c22 : p[b + 22]? = some (natConst 4 0) := by simpa using hcode 22 (by simp)
  have c23 : p[b + 23]? = some (natBranch 0 4 (b + 28) (b + 24)) := by simpa using hcode 23 (by simp)
  have c24 : p[b + 24]? = some (natStore 2 12) := by simpa using hcode 24 (by simp)
  have c25 : p[b + 25]? = some (natAdd 2 2 3) := by simpa using hcode 25 (by simp)
  have c26 : p[b + 26]? = some (natAdd 4 4 11) := by simpa using hcode 26 (by simp)
  have c27 : p[b + 27]? = some (jump (b + 23)) := by simpa using hcode 27 (by simp)
  intro r
  induction r with
  | zero =>
    intro i acc M R hi hL h11 h3 hA
    refine ⟨1, by omega, ?_⟩
    rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_at p b 6 _ rfl c6, run_zero]
    simp only [execInstr, show M 0 ≤ M 3 by omega, if_true]
    exact ⟨trivial, by simp [hA], fun a _ _ => trivial, trivial⟩
  | succ r ih =>
    intro i acc M R hi hL h11 h3 hA
    have hlt : ¬ M 0 ≤ M 3 := by omega
    obtain ⟨τ2, hτ2, r1, rA, rfr, rr⟩ := ih (i + 1) (acc + K)
      (Function.update (Function.update M 1 (acc + K)) 3 (i + 1)) R (by omega)
      (by simp [Function.update_apply, hL]) (by simp [Function.update_apply, h11])
      (by simp) (by simp [Function.update_apply])
    refine ⟨4 + τ2, by omega, ?_⟩
    have e4 : planarRAMRun p ⟨b + 6, M, R⟩ 4 =
        ⟨b + 6, Function.update (Function.update M 1 (acc + K)) 3 (i + 1), R⟩ := by
      rw [show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 from rfl, run_succ, step_at' p b 6 _ _ _ _ (by omega) c6,
        ex_brf _ _ _ _ _ _ _ hlt, run_succ, step_at' p b 7 _ _ _ _ (by omega) c7,
        ex_add _ _ _ _ _ _ _ (by rw [hA, hL]), run_succ, step_at' p b 8 _ _ _ _ (by omega) c8,
        ex_add _ _ _ _ _ _ _ (by simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte, h3, h11]; rfl),
        run_succ, step_at' p b 9 _ _ _ _ (by omega) c9, ex_jump, run_zero]
    rw [run_add, e4]
    refine ⟨r1, by rw [rA]; ring, fun a a3 aA => ?_, rr⟩
    rw [rfr a a3 aA, Function.update_of_ne a3, Function.update_of_ne aA]

set_option maxHeartbeats 4000000 in
lemma diag_loop (n : ℕ) :
    ∀ (r i : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), i + r = n →
      M 0 = n → M 11 = 1 → M 12 = 0 → M 3 = 2 * n + 2 → M 4 = i → M 2 = 36 + i * (2 * n + 2) →
      ∃ τ, τ ≤ 5 * r + 1 ∧ (planarRAMRun p ⟨b + 23, M, R⟩ τ).pc = b + 28 ∧
        (∀ v, i ≤ v → v < n → (planarRAMRun p ⟨b + 23, M, R⟩ τ).natMem (36 + v * (2 * n + 2)) = 0) ∧
        (∀ a, a ≠ 2 → a ≠ 4 → (∀ v, i ≤ v → v < n → a ≠ 36 + v * (2 * n + 2)) →
          (planarRAMRun p ⟨b + 23, M, R⟩ τ).natMem a = M a) ∧
        (planarRAMRun p ⟨b + 23, M, R⟩ τ).realMem = R := by
  have c0 : p[b + 0]? = some (natAdd 13 0 12) := by simpa using hcode 0 (by simp)
  have c1 : p[b + 1]? = some (natAdd 20 0 0) := by simpa using hcode 1 (by simp)
  have c2 : p[b + 2]? = some (natConst 19 2) := by simpa using hcode 2 (by simp)
  have c3 : p[b + 3]? = some (natAdd 31 0 11) := by simpa using hcode 3 (by simp)
  have c4 : p[b + 4]? = some (natConst 1 0) := by simpa using hcode 4 (by simp)
  have c5 : p[b + 5]? = some (natConst 3 0) := by simpa using hcode 5 (by simp)
  have c6 : p[b + 6]? = some (natBranch 0 3 (b + 10) (b + 7)) := by simpa using hcode 6 (by simp)
  have c7 : p[b + 7]? = some (natAdd 1 1 0) := by simpa using hcode 7 (by simp)
  have c8 : p[b + 8]? = some (natAdd 3 3 11) := by simpa using hcode 8 (by simp)
  have c9 : p[b + 9]? = some (jump (b + 6)) := by simpa using hcode 9 (by simp)
  have c10 : p[b + 10]? = some (natAdd 28 1 1) := by simpa using hcode 10 (by simp)
  have c11 : p[b + 11]? = some (natAdd 28 28 28) := by simpa using hcode 11 (by simp)
  have c12 : p[b + 12]? = some (natAdd 28 28 28) := by simpa using hcode 12 (by simp)
  have c13 : p[b + 13]? = some (natAdd 28 28 28) := by simpa using hcode 13 (by simp)
  have c14 : p[b + 14]? = some (natAdd 5 20 20) := by simpa using hcode 14 (by simp)
  have c15 : p[b + 15]? = some (natAdd 5 5 5) := by simpa using hcode 15 (by simp)
  have c16 : p[b + 16]? = some (natAdd 5 5 5) := by simpa using hcode 16 (by simp)
  have c17 : p[b + 17]? = some (natAdd 28 28 5) := by simpa using hcode 17 (by simp)
  have c18 : p[b + 18]? = some (natConst 5 48) := by simpa using hcode 18 (by simp)
  have c19 : p[b + 19]? = some (natAdd 28 28 5) := by simpa using hcode 19 (by simp)
  have c20 : p[b + 20]? = some (natConst 2 36) := by simpa using hcode 20 (by simp)
  have c21 : p[b + 21]? = some (natAdd 3 20 10) := by simpa using hcode 21 (by simp)
  have c22 : p[b + 22]? = some (natConst 4 0) := by simpa using hcode 22 (by simp)
  have c23 : p[b + 23]? = some (natBranch 0 4 (b + 28) (b + 24)) := by simpa using hcode 23 (by simp)
  have c24 : p[b + 24]? = some (natStore 2 12) := by simpa using hcode 24 (by simp)
  have c25 : p[b + 25]? = some (natAdd 2 2 3) := by simpa using hcode 25 (by simp)
  have c26 : p[b + 26]? = some (natAdd 4 4 11) := by simpa using hcode 26 (by simp)
  have c27 : p[b + 27]? = some (jump (b + 23)) := by simpa using hcode 27 (by simp)
  intro r
  induction r with
  | zero =>
    intro i M R hi h0 h11 h12 h3 h4 h2
    refine ⟨1, by omega, ?_⟩
    rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_at p b 23 _ rfl c23, run_zero]
    simp only [execInstr, show M 0 ≤ M 4 by omega, if_true]
    exact ⟨trivial, fun v h1 h2 => by omega, fun a _ _ _ => trivial, trivial⟩
  | succ r ih =>
    intro i M R hi h0 h11 h12 h3 h4 h2
    have hlt : ¬ M 0 ≤ M 4 := by omega
    have hp : 36 + i * (2 * n + 2) ≠ 2 ∧ 36 + i * (2 * n + 2) ≠ 4 ∧ 36 + i * (2 * n + 2) ≠ 0 ∧
      36 + i * (2 * n + 2) ≠ 11 ∧ 36 + i * (2 * n + 2) ≠ 12 ∧ 36 + i * (2 * n + 2) ≠ 3 := by
      have : 0 ≤ i * (2 * n + 2) := Nat.zero_le _; omega
    have hq : (0 : ℕ) ≠ 36 + i * (2 * n + 2) ∧ (2 : ℕ) ≠ 36 + i * (2 * n + 2) ∧ (3 : ℕ) ≠ 36 + i * (2 * n + 2) ∧
      (4 : ℕ) ≠ 36 + i * (2 * n + 2) ∧ (11 : ℕ) ≠ 36 + i * (2 * n + 2) ∧ (12 : ℕ) ≠ 36 + i * (2 * n + 2) := by
      have : 0 ≤ i * (2 * n + 2) := Nat.zero_le _; omega
    obtain ⟨τ2, hτ2, r1, rZ, rfr, rr⟩ := ih (i + 1)
      (Function.update (Function.update (Function.update M (36 + i * (2 * n + 2)) 0) 2 (36 + (i + 1) * (2 * n + 2)))
        4 (i + 1)) R (by omega)
      (by simp [Function.update_apply, h0, hp, hq]) (by simp [Function.update_apply, h11, hp, hq])
      (by simp [Function.update_apply, h12, hp, hq]) (by simp [Function.update_apply, h3, hp, hq]) (by simp)
      (by simp [Function.update_apply])
    refine ⟨5 + τ2, by omega, ?_⟩
    have e5 : planarRAMRun p ⟨b + 23, M, R⟩ 5 =
        ⟨b + 23, Function.update (Function.update (Function.update M (36 + i * (2 * n + 2)) 0) 2
          (36 + (i + 1) * (2 * n + 2))) 4 (i + 1), R⟩ := by
      rw [show (5 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 from rfl, run_succ, step_at' p b 23 _ _ _ _ (by omega) c23,
        ex_brf _ _ _ _ _ _ _ hlt, run_succ, step_at' p b 24 _ _ _ _ (by omega) c24,
        ex_store _ _ _ _ _ _ _ h2 h12, run_succ, step_at' p b 25 _ _ _ _ (by omega) c25,
        ex_add _ _ _ _ (36 + (i + 1) * (2 * n + 2)) _ _ (by simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte, hq, h2, h3, if_false]; ring),
        run_succ, step_at' p b 26 _ _ _ _ (by omega) c26,
        ex_add _ _ _ _ (i + 1) _ _ (by simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte, hq, h4, h11, if_false]),
        run_succ, step_at' p b 27 _ _ _ _ (by omega) c27, ex_jump, run_zero]
    rw [run_add, e5]
    refine ⟨r1, fun v hv1 hv2 => ?_, fun a a2 a4 aD => ?_, rr⟩
    · rcases Nat.eq_or_lt_of_le hv1 with h | h
      · subst h
        rw [rfr _ (by omega) (by omega) (fun v' h1 _ => by
          have := Nat.mul_le_mul_right (2 * n + 2) h1
          have e : (i + 1) * (2 * n + 2) = i * (2 * n + 2) + (2 * n + 2) := by ring
          omega)]
        simp [Function.update_apply, hp]
      · exact rZ v h hv2
    · rw [rfr a a2 a4 (fun v h1 h2 => aD v (by omega) h2), Function.update_of_ne a4, Function.update_of_ne a2,
        Function.update_of_ne (aD i le_rfl (by omega))]

set_option maxHeartbeats 8000000 in
lemma seg2 (n : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) (h0 : M 0 = n) (h10 : M 10 = 2) (h11 : M 11 = 1) (h12 : M 12 = 0) :
    ∃ τ, τ ≤ 9 * n + 24 ∧ (planarRAMRun p ⟨b, M, R⟩ τ).pc = b + 28 ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).natMem 13 = n ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 20 = 2 * n ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 19 = 2 ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 31 = n + 1 ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).natMem 11 = 1 ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 12 = 0 ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 10 = 2 ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 0 = n ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).natMem 1 = n * n ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 28 = 16 * (n * n) + 16 * n + 48 ∧
      (∀ v, v < n → (planarRAMRun p ⟨b, M, R⟩ τ).natMem (36 + v * (2 * n + 2)) = 0) ∧
      (∀ a, a ≠ 13 → a ≠ 20 → a ≠ 19 → a ≠ 31 → a ≠ 1 → a ≠ 3 → a ≠ 28 → a ≠ 5 → a ≠ 2 → a ≠ 4 →
        (∀ v, v < n → a ≠ 36 + v * (2 * n + 2)) → (planarRAMRun p ⟨b, M, R⟩ τ).natMem a = M a) ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).realMem = R := by
  have c0 : p[b + 0]? = some (natAdd 13 0 12) := by simpa using hcode 0 (by simp)
  have c1 : p[b + 1]? = some (natAdd 20 0 0) := by simpa using hcode 1 (by simp)
  have c2 : p[b + 2]? = some (natConst 19 2) := by simpa using hcode 2 (by simp)
  have c3 : p[b + 3]? = some (natAdd 31 0 11) := by simpa using hcode 3 (by simp)
  have c4 : p[b + 4]? = some (natConst 1 0) := by simpa using hcode 4 (by simp)
  have c5 : p[b + 5]? = some (natConst 3 0) := by simpa using hcode 5 (by simp)
  have c6 : p[b + 6]? = some (natBranch 0 3 (b + 10) (b + 7)) := by simpa using hcode 6 (by simp)
  have c7 : p[b + 7]? = some (natAdd 1 1 0) := by simpa using hcode 7 (by simp)
  have c8 : p[b + 8]? = some (natAdd 3 3 11) := by simpa using hcode 8 (by simp)
  have c9 : p[b + 9]? = some (jump (b + 6)) := by simpa using hcode 9 (by simp)
  have c10 : p[b + 10]? = some (natAdd 28 1 1) := by simpa using hcode 10 (by simp)
  have c11 : p[b + 11]? = some (natAdd 28 28 28) := by simpa using hcode 11 (by simp)
  have c12 : p[b + 12]? = some (natAdd 28 28 28) := by simpa using hcode 12 (by simp)
  have c13 : p[b + 13]? = some (natAdd 28 28 28) := by simpa using hcode 13 (by simp)
  have c14 : p[b + 14]? = some (natAdd 5 20 20) := by simpa using hcode 14 (by simp)
  have c15 : p[b + 15]? = some (natAdd 5 5 5) := by simpa using hcode 15 (by simp)
  have c16 : p[b + 16]? = some (natAdd 5 5 5) := by simpa using hcode 16 (by simp)
  have c17 : p[b + 17]? = some (natAdd 28 28 5) := by simpa using hcode 17 (by simp)
  have c18 : p[b + 18]? = some (natConst 5 48) := by simpa using hcode 18 (by simp)
  have c19 : p[b + 19]? = some (natAdd 28 28 5) := by simpa using hcode 19 (by simp)
  have c20 : p[b + 20]? = some (natConst 2 36) := by simpa using hcode 20 (by simp)
  have c21 : p[b + 21]? = some (natAdd 3 20 10) := by simpa using hcode 21 (by simp)
  have c22 : p[b + 22]? = some (natConst 4 0) := by simpa using hcode 22 (by simp)
  have c23 : p[b + 23]? = some (natBranch 0 4 (b + 28) (b + 24)) := by simpa using hcode 23 (by simp)
  have c24 : p[b + 24]? = some (natStore 2 12) := by simpa using hcode 24 (by simp)
  have c25 : p[b + 25]? = some (natAdd 2 2 3) := by simpa using hcode 25 (by simp)
  have c26 : p[b + 26]? = some (natAdd 4 4 11) := by simpa using hcode 26 (by simp)
  have c27 : p[b + 27]? = some (jump (b + 23)) := by simpa using hcode 27 (by simp)
  have sA : (planarRAMRun p ⟨b, M, R⟩ 6).pc = b + 6 ∧ (planarRAMRun p ⟨b, M, R⟩ 6).natMem 13 = n ∧ (planarRAMRun p ⟨b, M, R⟩ 6).natMem 20 = 2 * n ∧ (planarRAMRun p ⟨b, M, R⟩ 6).natMem 19 = 2 ∧
      (planarRAMRun p ⟨b, M, R⟩ 6).natMem 31 = n + 1 ∧ (planarRAMRun p ⟨b, M, R⟩ 6).natMem 1 = 0 ∧ (planarRAMRun p ⟨b, M, R⟩ 6).natMem 3 = 0 ∧
      (∀ a, a ≠ 13 → a ≠ 20 → a ≠ 19 → a ≠ 31 → a ≠ 1 → a ≠ 3 → (planarRAMRun p ⟨b, M, R⟩ 6).natMem a = M a) ∧ (planarRAMRun p ⟨b, M, R⟩ 6).realMem = R := by
    rw [show (6 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
    rw [run_succ, step_at' p b 0 _ _ _ _ (by omega) c0, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h0, h11, h12] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p b 1 _ _ _ _ (by omega) c1, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h0, h11, h12] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p b 2 _ _ _ _ (by omega) c2, ex_const]
    rw [run_succ, step_at' p b 3 _ _ _ _ (by omega) c3, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h0, h11, h12] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p b 4 _ _ _ _ (by omega) c4, ex_const]
    rw [run_succ, step_at' p b 5 _ _ _ _ (by omega) c5, ex_const]
    rw [run_zero]
    try rfl
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    all_goals first
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h0, h11, h12]; done)
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h0, h11, h12] <;> omega)
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h0, h11, h12]; ring1)
      | (intro a a13 a20 a19 a31 a1 a3; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, a13, a20, a19, a31, a1, a3])
  obtain ⟨a1, a13, a20, a19, a31, a1z, a3z, afr, ar⟩ := sA
  set S6 := planarRAMRun p ⟨b, M, R⟩ 6 with hS6
  obtain ⟨pc6, M6, R6⟩ := S6
  simp only at a1 a13 a20 a19 a31 a1z a3z afr ar
  subst a1; subst R6
  obtain ⟨τ1, hτ1, l1, l1v, lfr, lr⟩ := sqq_loop p b hcode n n 0 0 M6 R (by omega)
    (by rw [afr 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h0])
    (by rw [afr 11 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h11]) a3z a1z
  set S7 := planarRAMRun p ⟨b + 6, M6, R⟩ τ1 with hS7
  obtain ⟨pc7, M1, R7⟩ := S7
  simp only at l1 l1v lfr lr
  subst l1; subst R7
  have g1 : M1 1 = n * n := by rw [l1v]; ring
  have k1 : ∀ a, a ≠ 13 → a ≠ 20 → a ≠ 19 → a ≠ 31 → a ≠ 1 → a ≠ 3 → M1 a = M a := fun a a13 a20 a19 a31 a1 a3 => by rw [lfr a a3 a1, afr a a13 a20 a19 a31 a1 a3]
  have g20 : M1 20 = 2 * n := by rw [lfr 20 (by omega) (by omega), a20]
  have g10 : M1 10 = 2 := by rw [k1 10 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h10]
  have sB : (planarRAMRun p ⟨b + 10, M1, R⟩ 13).pc = b + 23 ∧ (planarRAMRun p ⟨b + 10, M1, R⟩ 13).natMem 28 = 16 * (n * n) + 16 * n + 48 ∧ (planarRAMRun p ⟨b + 10, M1, R⟩ 13).natMem 5 = 48 ∧
      (planarRAMRun p ⟨b + 10, M1, R⟩ 13).natMem 2 = 36 + 0 * (2 * n + 2) ∧ (planarRAMRun p ⟨b + 10, M1, R⟩ 13).natMem 3 = 2 * n + 2 ∧ (planarRAMRun p ⟨b + 10, M1, R⟩ 13).natMem 4 = 0 ∧
      (∀ a, a ≠ 28 → a ≠ 5 → a ≠ 2 → a ≠ 3 → a ≠ 4 → (planarRAMRun p ⟨b + 10, M1, R⟩ 13).natMem a = M1 a) ∧ (planarRAMRun p ⟨b + 10, M1, R⟩ 13).realMem = R := by
    rw [show (13 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
    rw [run_succ, step_at' p b 10 _ _ _ _ (by omega) c10, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g1, g20, g10] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p b 11 _ _ _ _ (by omega) c11, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g1, g20, g10] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p b 12 _ _ _ _ (by omega) c12, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g1, g20, g10] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p b 13 _ _ _ _ (by omega) c13, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g1, g20, g10] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p b 14 _ _ _ _ (by omega) c14, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g1, g20, g10] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p b 15 _ _ _ _ (by omega) c15, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g1, g20, g10] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p b 16 _ _ _ _ (by omega) c16, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g1, g20, g10] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p b 17 _ _ _ _ (by omega) c17, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g1, g20, g10] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p b 18 _ _ _ _ (by omega) c18, ex_const]
    rw [run_succ, step_at' p b 19 _ _ _ _ (by omega) c19, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g1, g20, g10] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p b 20 _ _ _ _ (by omega) c20, ex_const]
    rw [run_succ, step_at' p b 21 _ _ _ _ (by omega) c21, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g1, g20, g10] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p b 22 _ _ _ _ (by omega) c22, ex_const]
    rw [run_zero]
    try rfl
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    all_goals first
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, g1, g20, g10]; done)
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, g1, g20, g10] <;> omega)
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, g1, g20, g10]; ring1)
      | (intro a a28 a5 a2 a3 a4; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, a28, a5, a2, a3, a4])
  obtain ⟨b1, b28, b5, b2, b3, b4, bfr, br⟩ := sB
  set S8 := planarRAMRun p ⟨b + 10, M1, R⟩ 13 with hS8
  obtain ⟨pc8, M2, R8⟩ := S8
  simp only at b1 b28 b5 b2 b3 b4 bfr br
  subst b1; subst R8
  have k2 : ∀ a, a ≠ 13 → a ≠ 20 → a ≠ 19 → a ≠ 31 → a ≠ 1 → a ≠ 3 → a ≠ 28 → a ≠ 5 → a ≠ 2 → a ≠ 3 → a ≠ 4 → M2 a = M a := fun a a13 a20 a19 a31 a1 a3 a28 a5 a2 a3' a4 => by
    rw [bfr a a28 a5 a2 a3 a4, k1 a a13 a20 a19 a31 a1 a3]
  obtain ⟨τ2, hτ2, d1, dZ, dfr, dr⟩ := diag_loop p b hcode n n 0 M2 R (by omega)
    (by rw [k2 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h0])
    (by rw [k2 11 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h11])
    (by rw [k2 12 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h12])
    b3 b4 b2
  set S9 := planarRAMRun p ⟨b + 23, M2, R⟩ τ2 with hS9
  obtain ⟨pc9, M3, R9⟩ := S9
  simp only at d1 dZ dfr dr
  subst d1; subst R9
  have k3 : ∀ a, a ≠ 2 → a ≠ 4 → a < 36 → M3 a = M2 a := fun a a2 a4 ha =>
    dfr a a2 a4 (fun v _ _ => by have : 0 ≤ v * (2 * n + 2) := Nat.zero_le _; omega)
  refine ⟨6 + τ1 + 13 + τ2, by omega, ?_⟩
  rw [run_add, run_add, run_add, ← hS6, ← hS7, ← hS8, ← hS9]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun v hv => dZ v (Nat.zero_le _) hv, ?_, rfl⟩
  all_goals try (change M3 _ = _)
  · rw [k3 13 (by omega) (by omega) (by omega), bfr 13 (by omega) (by omega) (by omega) (by omega) (by omega),
      lfr 13 (by omega) (by omega), a13]
  · rw [k3 20 (by omega) (by omega) (by omega), bfr 20 (by omega) (by omega) (by omega) (by omega) (by omega), g20]
  · rw [k3 19 (by omega) (by omega) (by omega), bfr 19 (by omega) (by omega) (by omega) (by omega) (by omega),
      lfr 19 (by omega) (by omega), a19]
  · rw [k3 31 (by omega) (by omega) (by omega), bfr 31 (by omega) (by omega) (by omega) (by omega) (by omega),
      lfr 31 (by omega) (by omega), a31]
  · rw [k3 11 (by omega) (by omega) (by omega), k2 11 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h11]
  · rw [k3 12 (by omega) (by omega) (by omega), k2 12 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h12]
  · rw [k3 10 (by omega) (by omega) (by omega), k2 10 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h10]
  · rw [k3 0 (by omega) (by omega) (by omega), k2 0 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h0]
  · rw [k3 1 (by omega) (by omega) (by omega), bfr 1 (by omega) (by omega) (by omega) (by omega) (by omega), g1]
  · rw [k3 28 (by omega) (by omega) (by omega), b28]
  · intro a a13 a20 a19 a31 a1 a3 a28 a5 a2 a4 aD
    change M3 a = M a
    rw [dfr a a2 a4 (fun v _ hv => aD v hv), k2 a a13 a20 a19 a31 a1 a3 a28 a5 a2 a3 a4]

end

end SG2

open WilliamsonShmoys PlanarRAMInstruction
open Classical in
theorem solution (p : List PlanarRAMInstruction) (b : ℕ)
    (hcode : CodeAt p b
    [natAdd 13 0 12,
      natAdd 20 0 0,
      natConst 19 2,
      natAdd 31 0 11,
      natConst 1 0,
      natConst 3 0,
      natBranch 0 3 (b + 10) (b + 7),
      natAdd 1 1 0,
      natAdd 3 3 11,
      jump (b + 6),
      natAdd 28 1 1,
      natAdd 28 28 28,
      natAdd 28 28 28,
      natAdd 28 28 28,
      natAdd 5 20 20,
      natAdd 5 5 5,
      natAdd 5 5 5,
      natAdd 28 28 5,
      natConst 5 48,
      natAdd 28 28 5,
      natConst 2 36,
      natAdd 3 20 10,
      natConst 4 0,
      natBranch 0 4 (b + 28) (b + 24),
      natStore 2 12,
      natAdd 2 2 3,
      natAdd 4 4 11,
      jump (b + 23)])
    (n : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) (h0 : M 0 = n) (h10 : M 10 = 2) (h11 : M 11 = 1) (h12 : M 12 = 0) :
    ∃ τ, τ ≤ 9 * n + 24 ∧ (planarRAMRun p ⟨b, M, R⟩ τ).pc = b + 28 ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).natMem 13 = n ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 20 = 2 * n ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 19 = 2 ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 31 = n + 1 ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).natMem 11 = 1 ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 12 = 0 ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 10 = 2 ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 0 = n ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).natMem 1 = n * n ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 28 = 16 * (n * n) + 16 * n + 48 ∧
      (∀ v, v < n → (planarRAMRun p ⟨b, M, R⟩ τ).natMem (36 + v * (2 * n + 2)) = 0) ∧
      (∀ a, a ≠ 13 → a ≠ 20 → a ≠ 19 → a ≠ 31 → a ≠ 1 → a ≠ 3 → a ≠ 28 → a ≠ 5 → a ≠ 2 → a ≠ 4 →
        (∀ v, v < n → a ≠ 36 + v * (2 * n + 2)) → (planarRAMRun p ⟨b, M, R⟩ τ).natMem a = M a) ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).realMem = R :=
  SG2.seg2 p b hcode n M R h0 h10 h11 h12
