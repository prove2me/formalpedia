-- Prove2me | solution 1 for WilliamsonShmoys.ram_best_copy_select
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T08:23:09.38159+00:00
-- url     : https://prove2.me/submissions/73ee3a81-7b7e-47c1-919c-7dd30c8ddad7

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false

namespace BS
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
variable (p : List PlanarRAMInstruction) (q : ℕ)
  (hcode : CodeAt p q
    [natConst 0 0,
      natConst 2 1,
      natConst 4 2,
      natAdd 24 32 32,
      natAdd 18 28 24,
      natConst 26 0,
      natConst 6 0,
      natBranch 34 6 (q + 11) (q + 8),
      natAdd 26 26 32,
      natAdd 6 6 2,
      jump (q + 7),
      natConst 30 0,
      natConst 6 0,
      natBranch 26 6 (q + 17) (q + 14),
      natAdd 30 30 26,
      natAdd 6 6 2,
      jump (q + 13),
      natAdd 30 30 30,
      natConst 8 5,
      natAdd 14 30 8,
      natConst 6 0,
      natConst 20 0,
      natAdd 22 14 0,
      realZero 4,
      natBranch 34 6 (q + 50) (q + 25),
      realZero 2,
      natAdd 10 28 0,
      natConst 16 32,
      natAdd 12 14 0,
      natBranch 18 10 (q + 41) (q + 30),
      natLoad 8 12,
      natBranch 2 8 (q + 32) (q + 37),
      natLoad 8 10,
      natBranch 8 6 (q + 34) (q + 35),
      natBranch 6 8 (q + 37) (q + 35),
      realLoad 0 16,
      realAdd 2 2 0,
      natAdd 10 10 4,
      natAdd 12 12 4,
      natAdd 16 16 4,
      jump (q + 29),
      natBranch 6 0 (q + 43) (q + 42),
      realBranch 2 4 (q + 47) (q + 43),
      realZero 4,
      realAdd 4 4 2,
      natAdd 20 6 0,
      natAdd 22 14 0,
      natAdd 14 14 24,
      natAdd 6 6 2,
      jump (q + 24)])
include hcode

set_option maxHeartbeats 16000000 in
lemma vsum_loop (n LVB B c : ℕ) (D : ℕ → ℕ) (Rw : ℕ → ℝ) (hLe : LVB % 2 = 0) (hL : 40 ≤ LVB) (hB : B % 2 = 1) :
    ∀ (r v : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), v + r = n →
      (∀ a, (a % 2 = 1 ∨ 40 ≤ a) → M a = D a) → (∀ a, 6 ≤ a → R a = Rw a) →
      M 18 = LVB + 2 * n → M 10 = LVB + 2 * v → M 12 = B + 2 * v → M 16 = 32 + 2 * v →
      M 6 = c → M 2 = 1 → M 4 = 2 →
      ∃ τ, τ ≤ 12 * r + 1 ∧ (planarRAMRun p ⟨q + 29, M, R⟩ τ).pc = q + 41 ∧
        (planarRAMRun p ⟨q + 29, M, R⟩ τ).realMem 2 = R 2 + ∑ j ∈ Finset.Ico v n, (if 1 ≤ D (B + 2 * j) ∧ D (LVB + 2 * j) ≠ c then Rw (32 + 2 * j) else 0) ∧
        (∀ a, a ≠ 8 → a ≠ 10 → a ≠ 12 → a ≠ 16 → (planarRAMRun p ⟨q + 29, M, R⟩ τ).natMem a = M a) ∧
        (∀ a, a ≠ 0 → a ≠ 2 → (planarRAMRun p ⟨q + 29, M, R⟩ τ).realMem a = R a) := by
  have c0 : p[q + 0]? = some (natConst 0 0) := by simpa using hcode 0 (by simp)
  have c1 : p[q + 1]? = some (natConst 2 1) := by simpa using hcode 1 (by simp)
  have c2 : p[q + 2]? = some (natConst 4 2) := by simpa using hcode 2 (by simp)
  have c3 : p[q + 3]? = some (natAdd 24 32 32) := by simpa using hcode 3 (by simp)
  have c4 : p[q + 4]? = some (natAdd 18 28 24) := by simpa using hcode 4 (by simp)
  have c5 : p[q + 5]? = some (natConst 26 0) := by simpa using hcode 5 (by simp)
  have c6 : p[q + 6]? = some (natConst 6 0) := by simpa using hcode 6 (by simp)
  have c7 : p[q + 7]? = some (natBranch 34 6 (q + 11) (q + 8)) := by simpa using hcode 7 (by simp)
  have c8 : p[q + 8]? = some (natAdd 26 26 32) := by simpa using hcode 8 (by simp)
  have c9 : p[q + 9]? = some (natAdd 6 6 2) := by simpa using hcode 9 (by simp)
  have c10 : p[q + 10]? = some (jump (q + 7)) := by simpa using hcode 10 (by simp)
  have c11 : p[q + 11]? = some (natConst 30 0) := by simpa using hcode 11 (by simp)
  have c12 : p[q + 12]? = some (natConst 6 0) := by simpa using hcode 12 (by simp)
  have c13 : p[q + 13]? = some (natBranch 26 6 (q + 17) (q + 14)) := by simpa using hcode 13 (by simp)
  have c14 : p[q + 14]? = some (natAdd 30 30 26) := by simpa using hcode 14 (by simp)
  have c15 : p[q + 15]? = some (natAdd 6 6 2) := by simpa using hcode 15 (by simp)
  have c16 : p[q + 16]? = some (jump (q + 13)) := by simpa using hcode 16 (by simp)
  have c17 : p[q + 17]? = some (natAdd 30 30 30) := by simpa using hcode 17 (by simp)
  have c18 : p[q + 18]? = some (natConst 8 5) := by simpa using hcode 18 (by simp)
  have c19 : p[q + 19]? = some (natAdd 14 30 8) := by simpa using hcode 19 (by simp)
  have c20 : p[q + 20]? = some (natConst 6 0) := by simpa using hcode 20 (by simp)
  have c21 : p[q + 21]? = some (natConst 20 0) := by simpa using hcode 21 (by simp)
  have c22 : p[q + 22]? = some (natAdd 22 14 0) := by simpa using hcode 22 (by simp)
  have c23 : p[q + 23]? = some (realZero 4) := by simpa using hcode 23 (by simp)
  have c24 : p[q + 24]? = some (natBranch 34 6 (q + 50) (q + 25)) := by simpa using hcode 24 (by simp)
  have c25 : p[q + 25]? = some (realZero 2) := by simpa using hcode 25 (by simp)
  have c26 : p[q + 26]? = some (natAdd 10 28 0) := by simpa using hcode 26 (by simp)
  have c27 : p[q + 27]? = some (natConst 16 32) := by simpa using hcode 27 (by simp)
  have c28 : p[q + 28]? = some (natAdd 12 14 0) := by simpa using hcode 28 (by simp)
  have c29 : p[q + 29]? = some (natBranch 18 10 (q + 41) (q + 30)) := by simpa using hcode 29 (by simp)
  have c30 : p[q + 30]? = some (natLoad 8 12) := by simpa using hcode 30 (by simp)
  have c31 : p[q + 31]? = some (natBranch 2 8 (q + 32) (q + 37)) := by simpa using hcode 31 (by simp)
  have c32 : p[q + 32]? = some (natLoad 8 10) := by simpa using hcode 32 (by simp)
  have c33 : p[q + 33]? = some (natBranch 8 6 (q + 34) (q + 35)) := by simpa using hcode 33 (by simp)
  have c34 : p[q + 34]? = some (natBranch 6 8 (q + 37) (q + 35)) := by simpa using hcode 34 (by simp)
  have c35 : p[q + 35]? = some (realLoad 0 16) := by simpa using hcode 35 (by simp)
  have c36 : p[q + 36]? = some (realAdd 2 2 0) := by simpa using hcode 36 (by simp)
  have c37 : p[q + 37]? = some (natAdd 10 10 4) := by simpa using hcode 37 (by simp)
  have c38 : p[q + 38]? = some (natAdd 12 12 4) := by simpa using hcode 38 (by simp)
  have c39 : p[q + 39]? = some (natAdd 16 16 4) := by simpa using hcode 39 (by simp)
  have c40 : p[q + 40]? = some (jump (q + 29)) := by simpa using hcode 40 (by simp)
  have c41 : p[q + 41]? = some (natBranch 6 0 (q + 43) (q + 42)) := by simpa using hcode 41 (by simp)
  have c42 : p[q + 42]? = some (realBranch 2 4 (q + 47) (q + 43)) := by simpa using hcode 42 (by simp)
  have c43 : p[q + 43]? = some (realZero 4) := by simpa using hcode 43 (by simp)
  have c44 : p[q + 44]? = some (realAdd 4 4 2) := by simpa using hcode 44 (by simp)
  have c45 : p[q + 45]? = some (natAdd 20 6 0) := by simpa using hcode 45 (by simp)
  have c46 : p[q + 46]? = some (natAdd 22 14 0) := by simpa using hcode 46 (by simp)
  have c47 : p[q + 47]? = some (natAdd 14 14 24) := by simpa using hcode 47 (by simp)
  have c48 : p[q + 48]? = some (natAdd 6 6 2) := by simpa using hcode 48 (by simp)
  have c49 : p[q + 49]? = some (jump (q + 24)) := by simpa using hcode 49 (by simp)
  intro r
  induction r with
  | zero =>
    intro v M R hv hD hRw h18 h10 h12 h16 h6 h2 h4
    refine ⟨1, by omega, ?_⟩
    rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_at p q 29 _ rfl c29, run_zero]
    simp only [execInstr, show M 18 ≤ M 10 by omega, if_true]
    refine ⟨trivial, ?_, fun a _ _ _ _ => trivial, fun a _ _ => trivial⟩
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero]
  | succ r ih =>
    intro v M R hv hD hRw h18 h10 h12 h16 h6 h2 h4
    have hlt : ¬ M 18 ≤ M 10 := by omega
    have hvn : v < n := by omega
    have hne : LVB + 2 * v ≠ 8 ∧ B + 2 * v ≠ 8 ∧ (32 + 2 * v ≠ 0) ∧ LVB + 2 * v ≠ 0 := by omega
    obtain ⟨bt, hb⟩ : ∃ bt, M (B + 2 * v) = bt := ⟨_, rfl⟩
    obtain ⟨md, hm⟩ : ∃ md, M (LVB + 2 * v) = md := ⟨_, rfl⟩
    obtain ⟨wv, hR⟩ : ∃ wv, R (32 + 2 * v) = wv := ⟨_, rfl⟩
    have hbD : D (B + 2 * v) = bt := by rw [← hb, hD _ (Or.inl (by omega))]
    have hmD : D (LVB + 2 * v) = md := by rw [← hm, hD _ (Or.inr (by omega))]
    have hwD : Rw (32 + 2 * v) = wv := by rw [← hR, hRw _ (by omega)]
    have one : ∃ τ1, τ1 ≤ 12 ∧ (planarRAMRun p ⟨q + 29, M, R⟩ τ1).pc = q + 29 ∧
        (planarRAMRun p ⟨q + 29, M, R⟩ τ1).realMem 2 = R 2 + (if 1 ≤ bt ∧ md ≠ c then wv else 0) ∧
        (planarRAMRun p ⟨q + 29, M, R⟩ τ1).natMem 10 = LVB + 2 * (v + 1) ∧ (planarRAMRun p ⟨q + 29, M, R⟩ τ1).natMem 12 = B + 2 * (v + 1) ∧
        (planarRAMRun p ⟨q + 29, M, R⟩ τ1).natMem 16 = 32 + 2 * (v + 1) ∧
        (∀ a, a ≠ 8 → a ≠ 10 → a ≠ 12 → a ≠ 16 → (planarRAMRun p ⟨q + 29, M, R⟩ τ1).natMem a = M a) ∧
        (∀ a, a ≠ 0 → a ≠ 2 → (planarRAMRun p ⟨q + 29, M, R⟩ τ1).realMem a = R a) := by
      by_cases a0 : 1 ≤ bt
      · by_cases a1 : md ≤ c
        · by_cases a2 : c ≤ md
          · have hc : ¬ (1 ≤ bt ∧ md ≠ c) := by omega
            refine ⟨10, by omega, ?_⟩
            rw [show (10 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
            rw [run_succ, step_at' p q 29 _ _ _ _ (by omega) c29, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2] <;> first | trivial | omega)]
            rw [run_succ, step_at' p q 30 _ _ _ _ (by omega) c30, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p q 31 _ _ _ _ (by omega) c31, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2] <;> first | trivial | omega)]
            rw [run_succ, step_at' p q 32 _ _ _ _ (by omega) c32, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p q 33 _ _ _ _ (by omega) c33, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2] <;> first | trivial | omega)]
            rw [run_succ, step_at' p q 34 _ _ _ _ (by omega) c34, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2] <;> first | trivial | omega)]
            rw [run_succ, step_at' p q 37 _ _ _ _ (by omega) c37, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p q 38 _ _ _ _ (by omega) c38, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p q 39 _ _ _ _ (by omega) c39, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p q 40 _ _ _ _ (by omega) c40, ex_jump]
            rw [run_zero]
            try rfl
            refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
            all_goals first
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, if_neg hc]; done)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2, if_neg hc]; done)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2, if_neg hc] <;> omega)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2, if_neg hc]; ring1)
              | (intro a a8 a10 a12 a16; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, a8, a10, a12, a16])
              | (intro a a0 a2; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, a0, a2])
          · have hc : 1 ≤ bt ∧ md ≠ c := ⟨a0, by omega⟩
            refine ⟨12, by omega, ?_⟩
            rw [show (12 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
            rw [run_succ, step_at' p q 29 _ _ _ _ (by omega) c29, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2] <;> first | trivial | omega)]
            rw [run_succ, step_at' p q 30 _ _ _ _ (by omega) c30, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p q 31 _ _ _ _ (by omega) c31, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2] <;> first | trivial | omega)]
            rw [run_succ, step_at' p q 32 _ _ _ _ (by omega) c32, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p q 33 _ _ _ _ (by omega) c33, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2] <;> first | trivial | omega)]
            rw [run_succ, step_at' p q 34 _ _ _ _ (by omega) c34, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2] <;> first | trivial | omega)]
            rw [run_succ, step_at' p q 35 _ _ _ _ (by omega) c35, ex_rload _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2] <;> first | rfl | omega) | rfl) (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p q 36 _ _ _ _ (by omega) c36, ex_radd _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p q 37 _ _ _ _ (by omega) c37, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p q 38 _ _ _ _ (by omega) c38, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p q 39 _ _ _ _ (by omega) c39, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p q 40 _ _ _ _ (by omega) c40, ex_jump]
            rw [run_zero]
            try rfl
            refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
            all_goals first
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, if_pos hc]; done)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2, if_pos hc]; done)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2, if_pos hc] <;> omega)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, a2, if_pos hc]; ring1)
              | (intro a a8 a10 a12 a16; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, a8, a10, a12, a16])
              | (intro a a0 a2; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, a0, a2])
        · have hc : 1 ≤ bt ∧ md ≠ c := ⟨a0, by omega⟩
          refine ⟨11, by omega, ?_⟩
          rw [show (11 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
          rw [run_succ, step_at' p q 29 _ _ _ _ (by omega) c29, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1] <;> first | trivial | omega)]
          rw [run_succ, step_at' p q 30 _ _ _ _ (by omega) c30, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p q 31 _ _ _ _ (by omega) c31, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1] <;> first | trivial | omega)]
          rw [run_succ, step_at' p q 32 _ _ _ _ (by omega) c32, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p q 33 _ _ _ _ (by omega) c33, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1] <;> first | trivial | omega)]
          rw [run_succ, step_at' p q 35 _ _ _ _ (by omega) c35, ex_rload _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1] <;> first | rfl | omega) | rfl) (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p q 36 _ _ _ _ (by omega) c36, ex_radd _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p q 37 _ _ _ _ (by omega) c37, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p q 38 _ _ _ _ (by omega) c38, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p q 39 _ _ _ _ (by omega) c39, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p q 40 _ _ _ _ (by omega) c40, ex_jump]
          rw [run_zero]
          try rfl
          refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
          all_goals first
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, if_pos hc]; done)
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, if_pos hc]; done)
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, if_pos hc] <;> omega)
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, a1, if_pos hc]; ring1)
            | (intro a a8 a10 a12 a16; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, a8, a10, a12, a16])
            | (intro a a0 a2; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, a0, a2])
      · have hc : ¬ (1 ≤ bt ∧ md ≠ c) := by omega
        refine ⟨7, by omega, ?_⟩
        rw [show (7 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
        rw [run_succ, step_at' p q 29 _ _ _ _ (by omega) c29, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0] <;> first | trivial | omega)]
        rw [run_succ, step_at' p q 30 _ _ _ _ (by omega) c30, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0] <;> first | rfl | omega) | rfl)]
        rw [run_succ, step_at' p q 31 _ _ _ _ (by omega) c31, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0] <;> first | trivial | omega)]
        rw [run_succ, step_at' p q 37 _ _ _ _ (by omega) c37, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0] <;> first | rfl | omega) | rfl)]
        rw [run_succ, step_at' p q 38 _ _ _ _ (by omega) c38, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0] <;> first | rfl | omega) | rfl)]
        rw [run_succ, step_at' p q 39 _ _ _ _ (by omega) c39, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0] <;> first | rfl | omega) | rfl)]
        rw [run_succ, step_at' p q 40 _ _ _ _ (by omega) c40, ex_jump]
        rw [run_zero]
        try rfl
        refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals first
          | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, if_neg hc]; done)
          | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, if_neg hc]; done)
          | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, if_neg hc] <;> omega)
          | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h16, h6, h2, h4, hlt, hb, hm, hR, hne, a0, if_neg hc]; ring1)
          | (intro a a8 a10 a12 a16; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, a8, a10, a12, a16])
          | (intro a a0 a2; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, a0, a2])
    obtain ⟨τ1, hτ1, q1, q2, q10, q12, q16, qfr, qRfr⟩ := one
    set S1 := planarRAMRun p ⟨q + 29, M, R⟩ τ1 with hS1
    obtain ⟨pc1, M1, R1⟩ := S1
    simp only at q1 q2 q10 q12 q16 qfr qRfr
    subst q1
    obtain ⟨τ2, hτ2, r1, r2, rfr, rRfr⟩ := ih (v + 1) M1 R1 (by omega)
      (fun a ha => by rw [qfr a (by omega) (by omega) (by omega) (by omega), hD a ha])
      (fun a ha => by rw [qRfr a (by omega) (by omega), hRw a ha])
      (by rw [qfr 18 (by omega) (by omega) (by omega) (by omega), h18]) q10 q12 q16
      (by rw [qfr 6 (by omega) (by omega) (by omega) (by omega), h6])
      (by rw [qfr 2 (by omega) (by omega) (by omega) (by omega), h2])
      (by rw [qfr 4 (by omega) (by omega) (by omega) (by omega), h4])
    refine ⟨τ1 + τ2, by omega, ?_⟩
    rw [run_add, ← hS1]
    refine ⟨r1, ?_, fun a a8 a10 a12 a16 => ?_, fun a a0 a2 => ?_⟩
    · rw [r2, q2, Finset.sum_eq_sum_Ico_succ_bot hvn, hbD, hmD, hwD]; ring
    · rw [rfr a a8 a10 a12 a16, qfr a a8 a10 a12 a16]
    · rw [rRfr a a0 a2, qRfr a a0 a2]

set_option maxHeartbeats 16000000 in
lemma csel_loop (n k LVB B0 : ℕ) (D : ℕ → ℕ) (Rw : ℕ → ℝ) (hLe : LVB % 2 = 0) (hL : 40 ≤ LVB)
    (hB : B0 % 2 = 1) :
    ∀ (r c : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), c + r = k →
      (∀ a, (a % 2 = 1 ∨ 40 ≤ a) → M a = D a) → (∀ a, 6 ≤ a → R a = Rw a) →
      M 34 = k → M 6 = c → M 14 = B0 + 2 * c * n → M 28 = LVB → M 18 = LVB + 2 * n → M 24 = 2 * n →
      M 0 = 0 → M 2 = 1 → M 4 = 2 → (c = 0 ∨ (M 20 < c ∧ R 4 = (∑ j ∈ Finset.range n, if 1 ≤ D (B0 + 2 * M 20 * n + 2 * j) ∧ D (LVB + 2 * j) ≠ M 20 then Rw (32 + 2 * j) else 0) ∧ M 22 = B0 + 2 * M 20 * n ∧ ∀ c', c' < c → (∑ j ∈ Finset.range n, if 1 ≤ D (B0 + 2 * c' * n + 2 * j) ∧ D (LVB + 2 * j) ≠ c' then Rw (32 + 2 * j) else 0) ≤ R 4)) →
      ∃ τ, τ ≤ (12 * n + 20) * r + 1 ∧ (planarRAMRun p ⟨q + 24, M, R⟩ τ).pc = q + 50 ∧ (k = 0 ∨ ((planarRAMRun p ⟨q + 24, M, R⟩ τ).natMem 20 < k ∧ (planarRAMRun p ⟨q + 24, M, R⟩ τ).realMem 4 = (∑ j ∈ Finset.range n, if 1 ≤ D (B0 + 2 * (planarRAMRun p ⟨q + 24, M, R⟩ τ).natMem 20 * n + 2 * j) ∧ D (LVB + 2 * j) ≠ (planarRAMRun p ⟨q + 24, M, R⟩ τ).natMem 20 then Rw (32 + 2 * j) else 0) ∧ (planarRAMRun p ⟨q + 24, M, R⟩ τ).natMem 22 = B0 + 2 * (planarRAMRun p ⟨q + 24, M, R⟩ τ).natMem 20 * n ∧ ∀ c', c' < k → (∑ j ∈ Finset.range n, if 1 ≤ D (B0 + 2 * c' * n + 2 * j) ∧ D (LVB + 2 * j) ≠ c' then Rw (32 + 2 * j) else 0) ≤ (planarRAMRun p ⟨q + 24, M, R⟩ τ).realMem 4)) ∧
        (∀ a, a ≠ 6 → a ≠ 8 → a ≠ 10 → a ≠ 12 → a ≠ 14 → a ≠ 16 → a ≠ 20 → a ≠ 22 → (planarRAMRun p ⟨q + 24, M, R⟩ τ).natMem a = M a) ∧
        (∀ a, 6 ≤ a → (planarRAMRun p ⟨q + 24, M, R⟩ τ).realMem a = R a) := by
  have c0 : p[q + 0]? = some (natConst 0 0) := by simpa using hcode 0 (by simp)
  have c1 : p[q + 1]? = some (natConst 2 1) := by simpa using hcode 1 (by simp)
  have c2 : p[q + 2]? = some (natConst 4 2) := by simpa using hcode 2 (by simp)
  have c3 : p[q + 3]? = some (natAdd 24 32 32) := by simpa using hcode 3 (by simp)
  have c4 : p[q + 4]? = some (natAdd 18 28 24) := by simpa using hcode 4 (by simp)
  have c5 : p[q + 5]? = some (natConst 26 0) := by simpa using hcode 5 (by simp)
  have c6 : p[q + 6]? = some (natConst 6 0) := by simpa using hcode 6 (by simp)
  have c7 : p[q + 7]? = some (natBranch 34 6 (q + 11) (q + 8)) := by simpa using hcode 7 (by simp)
  have c8 : p[q + 8]? = some (natAdd 26 26 32) := by simpa using hcode 8 (by simp)
  have c9 : p[q + 9]? = some (natAdd 6 6 2) := by simpa using hcode 9 (by simp)
  have c10 : p[q + 10]? = some (jump (q + 7)) := by simpa using hcode 10 (by simp)
  have c11 : p[q + 11]? = some (natConst 30 0) := by simpa using hcode 11 (by simp)
  have c12 : p[q + 12]? = some (natConst 6 0) := by simpa using hcode 12 (by simp)
  have c13 : p[q + 13]? = some (natBranch 26 6 (q + 17) (q + 14)) := by simpa using hcode 13 (by simp)
  have c14 : p[q + 14]? = some (natAdd 30 30 26) := by simpa using hcode 14 (by simp)
  have c15 : p[q + 15]? = some (natAdd 6 6 2) := by simpa using hcode 15 (by simp)
  have c16 : p[q + 16]? = some (jump (q + 13)) := by simpa using hcode 16 (by simp)
  have c17 : p[q + 17]? = some (natAdd 30 30 30) := by simpa using hcode 17 (by simp)
  have c18 : p[q + 18]? = some (natConst 8 5) := by simpa using hcode 18 (by simp)
  have c19 : p[q + 19]? = some (natAdd 14 30 8) := by simpa using hcode 19 (by simp)
  have c20 : p[q + 20]? = some (natConst 6 0) := by simpa using hcode 20 (by simp)
  have c21 : p[q + 21]? = some (natConst 20 0) := by simpa using hcode 21 (by simp)
  have c22 : p[q + 22]? = some (natAdd 22 14 0) := by simpa using hcode 22 (by simp)
  have c23 : p[q + 23]? = some (realZero 4) := by simpa using hcode 23 (by simp)
  have c24 : p[q + 24]? = some (natBranch 34 6 (q + 50) (q + 25)) := by simpa using hcode 24 (by simp)
  have c25 : p[q + 25]? = some (realZero 2) := by simpa using hcode 25 (by simp)
  have c26 : p[q + 26]? = some (natAdd 10 28 0) := by simpa using hcode 26 (by simp)
  have c27 : p[q + 27]? = some (natConst 16 32) := by simpa using hcode 27 (by simp)
  have c28 : p[q + 28]? = some (natAdd 12 14 0) := by simpa using hcode 28 (by simp)
  have c29 : p[q + 29]? = some (natBranch 18 10 (q + 41) (q + 30)) := by simpa using hcode 29 (by simp)
  have c30 : p[q + 30]? = some (natLoad 8 12) := by simpa using hcode 30 (by simp)
  have c31 : p[q + 31]? = some (natBranch 2 8 (q + 32) (q + 37)) := by simpa using hcode 31 (by simp)
  have c32 : p[q + 32]? = some (natLoad 8 10) := by simpa using hcode 32 (by simp)
  have c33 : p[q + 33]? = some (natBranch 8 6 (q + 34) (q + 35)) := by simpa using hcode 33 (by simp)
  have c34 : p[q + 34]? = some (natBranch 6 8 (q + 37) (q + 35)) := by simpa using hcode 34 (by simp)
  have c35 : p[q + 35]? = some (realLoad 0 16) := by simpa using hcode 35 (by simp)
  have c36 : p[q + 36]? = some (realAdd 2 2 0) := by simpa using hcode 36 (by simp)
  have c37 : p[q + 37]? = some (natAdd 10 10 4) := by simpa using hcode 37 (by simp)
  have c38 : p[q + 38]? = some (natAdd 12 12 4) := by simpa using hcode 38 (by simp)
  have c39 : p[q + 39]? = some (natAdd 16 16 4) := by simpa using hcode 39 (by simp)
  have c40 : p[q + 40]? = some (jump (q + 29)) := by simpa using hcode 40 (by simp)
  have c41 : p[q + 41]? = some (natBranch 6 0 (q + 43) (q + 42)) := by simpa using hcode 41 (by simp)
  have c42 : p[q + 42]? = some (realBranch 2 4 (q + 47) (q + 43)) := by simpa using hcode 42 (by simp)
  have c43 : p[q + 43]? = some (realZero 4) := by simpa using hcode 43 (by simp)
  have c44 : p[q + 44]? = some (realAdd 4 4 2) := by simpa using hcode 44 (by simp)
  have c45 : p[q + 45]? = some (natAdd 20 6 0) := by simpa using hcode 45 (by simp)
  have c46 : p[q + 46]? = some (natAdd 22 14 0) := by simpa using hcode 46 (by simp)
  have c47 : p[q + 47]? = some (natAdd 14 14 24) := by simpa using hcode 47 (by simp)
  have c48 : p[q + 48]? = some (natAdd 6 6 2) := by simpa using hcode 48 (by simp)
  have c49 : p[q + 49]? = some (jump (q + 24)) := by simpa using hcode 49 (by simp)
  intro r
  induction r with
  | zero =>
    intro c M R hc hD hRw h34 h6 h14 h28 h18 h24 h0 h2 h4 hinv
    refine ⟨1, by omega, ?_⟩
    rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_at p q 24 _ rfl c24, run_zero]
    simp only [execInstr, show M 34 ≤ M 6 by omega, if_true]
    refine ⟨trivial, ?_, fun a _ _ _ _ _ _ _ _ => trivial, fun a _ => trivial⟩
    have : c = k := by omega
    subst this; exact hinv
  | succ r ih =>
    intro c M R hc hD hRw h34 h6 h14 h28 h18 h24 h0 h2 h4 hinv
    have hlt : ¬ M 34 ≤ M 6 := by omega
    have sA : (planarRAMRun p ⟨q + 24, M, R⟩ 5).pc = q + 29 ∧ (planarRAMRun p ⟨q + 24, M, R⟩ 5).natMem 10 = LVB + 2 * 0 ∧ (planarRAMRun p ⟨q + 24, M, R⟩ 5).natMem 16 = 32 + 2 * 0 ∧
        (planarRAMRun p ⟨q + 24, M, R⟩ 5).natMem 12 = B0 + 2 * c * n + 2 * 0 ∧
        (∀ a, a ≠ 10 → a ≠ 16 → a ≠ 12 → (planarRAMRun p ⟨q + 24, M, R⟩ 5).natMem a = M a) ∧
        (∀ a, a ≠ 2 → (planarRAMRun p ⟨q + 24, M, R⟩ 5).realMem a = R a) ∧ (planarRAMRun p ⟨q + 24, M, R⟩ 5).realMem 2 = 0 := by
      rw [show (5 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 from rfl]
      rw [run_succ, step_at' p q 24 _ _ _ _ (by omega) c24, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h34, h6, h14, h28, h0, hlt] <;> first | trivial | omega)]
      rw [run_succ, step_at' p q 25 _ _ _ _ (by omega) c25, ex_rzero]
      rw [run_succ, step_at' p q 26 _ _ _ _ (by omega) c26, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h34, h6, h14, h28, h0, hlt] <;> first | rfl | omega) | rfl)]
      rw [run_succ, step_at' p q 27 _ _ _ _ (by omega) c27, ex_const]
      rw [run_succ, step_at' p q 28 _ _ _ _ (by omega) c28, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h34, h6, h14, h28, h0, hlt] <;> first | rfl | omega) | rfl)]
      rw [run_zero]
      try rfl
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first
        | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h34, h6, h14, h28, h0, hlt]; done)
        | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h34, h6, h14, h28, h0, hlt] <;> omega)
        | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h34, h6, h14, h28, h0, hlt]; ring1)
        | (intro a a10 a16 a12; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, a10, a16, a12])
        | (intro a a2; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, a2])
    obtain ⟨a1, a10, a16, a12, afr, aRfr, a2r⟩ := sA
    set S5 := planarRAMRun p ⟨q + 24, M, R⟩ 5 with hS5
    obtain ⟨pc5, M5, R5⟩ := S5
    simp only at a1 a10 a16 a12 afr aRfr a2r
    subst a1
    have hBc : (B0 + 2 * c * n) % 2 = 1 := by
      have e : 2 * c * n = 2 * (c * n) := by ring
      omega
    obtain ⟨τv, hτv, v1, v2, vfr, vRfr⟩ := vsum_loop p q hcode n LVB (B0 + 2 * c * n) c D Rw hLe hL hBc n 0 M5 R5
      (by omega) (fun a ha => by rw [afr a (by omega) (by omega) (by omega), hD a ha])
      (fun a ha => by rw [aRfr a (by omega), hRw a ha])
      (by rw [afr 18 (by omega) (by omega) (by omega), h18]) a10 (by rw [a12]) a16
      (by rw [afr 6 (by omega) (by omega) (by omega), h6]) (by rw [afr 2 (by omega) (by omega) (by omega), h2])
      (by rw [afr 4 (by omega) (by omega) (by omega), h4])
    set S6 := planarRAMRun p ⟨q + 29, M5, R5⟩ τv with hS6
    obtain ⟨pc6, M6, R6⟩ := S6
    simp only at v1 v2 vfr vRfr
    subst v1
    have mm : ∀ a, a ≠ 6 → a ≠ 8 → a ≠ 10 → a ≠ 12 → a ≠ 14 → a ≠ 16 → a ≠ 20 → a ≠ 22 → M6 a = M a :=
      fun a a6 a8 a10 a12 a14 a16 a20 a22 => by rw [vfr a a8 a10 a12 a16, afr a a10 a16 a12]
    have m6 : M6 6 = c := by rw [vfr 6 (by omega) (by omega) (by omega) (by omega), afr 6 (by omega) (by omega) (by omega), h6]
    have m0 : M6 0 = 0 := by rw [vfr 0 (by omega) (by omega) (by omega) (by omega), afr 0 (by omega) (by omega) (by omega), h0]
    have m14 : M6 14 = B0 + 2 * c * n := by rw [vfr 14 (by omega) (by omega) (by omega) (by omega), afr 14 (by omega) (by omega) (by omega), h14]
    have m24 : M6 24 = 2 * n := by rw [vfr 24 (by omega) (by omega) (by omega) (by omega), afr 24 (by omega) (by omega) (by omega), h24]
    have m2 : M6 2 = 1 := by rw [vfr 2 (by omega) (by omega) (by omega) (by omega), afr 2 (by omega) (by omega) (by omega), h2]
    have m20 : M6 20 = M 20 := by rw [vfr 20 (by omega) (by omega) (by omega) (by omega), afr 20 (by omega) (by omega) (by omega)]
    have m22 : M6 22 = M 22 := by rw [vfr 22 (by omega) (by omega) (by omega) (by omega), afr 22 (by omega) (by omega) (by omega)]
    have racc : R6 2 = (∑ j ∈ Finset.range n, if 1 ≤ D (B0 + 2 * c * n + 2 * j) ∧ D (LVB + 2 * j) ≠ c then Rw (32 + 2 * j) else 0) := by
      rw [v2, a2r, zero_add, Finset.range_eq_Ico]
    have r4 : R6 4 = R 4 := by rw [vRfr 4 (by omega) (by omega), aRfr 4 (by omega)]
    -- the three tails, each giving the invariant for c + 1
    have tl3 : ∃ τt, τt ≤ 9 ∧ (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).pc = q + 24 ∧
        (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).natMem 6 = c + 1 ∧
        (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).natMem 14 = B0 + 2 * (c + 1) * n ∧
        ((c + 1) = 0 ∨ ((planarRAMRun p ⟨q + 41, M6, R6⟩ τt).natMem 20 < c + 1 ∧
          (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).realMem 4 = (∑ j ∈ Finset.range n, if 1 ≤ D (B0 + 2 * (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).natMem 20 * n + 2 * j) ∧ D (LVB + 2 * j) ≠ (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).natMem 20 then Rw (32 + 2 * j) else 0) ∧
          (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).natMem 22 = B0 + 2 * (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).natMem 20 * n ∧
          ∀ c', c' < c + 1 → (∑ j ∈ Finset.range n, if 1 ≤ D (B0 + 2 * c' * n + 2 * j) ∧ D (LVB + 2 * j) ≠ c' then Rw (32 + 2 * j) else 0) ≤ (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).realMem 4)) ∧
        (∀ a, a ≠ 6 → a ≠ 14 → a ≠ 20 → a ≠ 22 → (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).natMem a = M6 a) ∧
        (∀ a, a ≠ 4 → (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).realMem a = R6 a) := by
      by_cases hc0 : c = 0
      · have b1 : M6 6 ≤ M6 0 := by omega
        have tl : ∃ τt, τt ≤ 9 ∧ (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).pc = q + 24 ∧ (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).natMem 6 = c + 1 ∧ (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).natMem 14 = B0 + 2 * (c + 1) * n ∧
          (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).natMem 20 = c ∧ (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).natMem 22 = B0 + 2 * c * n ∧ (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).realMem 4 = R6 2 ∧
          (∀ a, a ≠ 6 → a ≠ 14 → a ≠ 20 → a ≠ 22 → (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).natMem a = M6 a) ∧
          (∀ a, a ≠ 4 → (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).realMem a = R6 a) := by
          refine ⟨8, by omega, ?_⟩
          rw [show (8 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
          rw [run_succ, step_at' p q 41 _ _ _ _ (by omega) c41, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, m6, m0, m14, m24, m2, b1] <;> first | trivial | omega)]
          rw [run_succ, step_at' p q 43 _ _ _ _ (by omega) c43, ex_rzero]
          rw [run_succ, step_at' p q 44 _ _ _ _ (by omega) c44, ex_radd _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, m6, m0, m14, m24, m2, b1] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p q 45 _ _ _ _ (by omega) c45, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, m6, m0, m14, m24, m2, b1] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p q 46 _ _ _ _ (by omega) c46, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, m6, m0, m14, m24, m2, b1] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p q 47 _ _ _ _ (by omega) c47, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, m6, m0, m14, m24, m2, b1] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p q 48 _ _ _ _ (by omega) c48, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, m6, m0, m14, m24, m2, b1] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p q 49 _ _ _ _ (by omega) c49, ex_jump]
          rw [run_zero]
          try rfl
          refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          all_goals first
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, m6, m0, m14, m24, m2, b1]; done)
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, m6, m0, m14, m24, m2, b1] <;> omega)
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, m6, m0, m14, m24, m2, b1]; ring1)
            | (intro a a6 a14 a20 a22; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, a6, a14, a20, a22])
            | (intro a a4; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, a4])
        obtain ⟨τt, hτt, t1, t6, t14, t20, t22, t4, tfr, tRfr⟩ := tl
        refine ⟨τt, hτt, t1, t6, t14, Or.inr ⟨by omega, ?_, ?_, fun c' hc' => ?_⟩, tfr, tRfr⟩
        · rw [t4, t20, racc]
        · rw [t22, t20]
        · have : c' = c := by omega
          subst this; rw [t4, racc]
      · have b1 : ¬ M6 6 ≤ M6 0 := by omega
        obtain ⟨hbc, hb4, hb22, hball⟩ := hinv.resolve_left hc0
        by_cases hle : R6 2 ≤ R6 4
        · have tl : ∃ τt, τt ≤ 9 ∧ (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).pc = q + 24 ∧
              (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).natMem 6 = c + 1 ∧
              (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).natMem 14 = B0 + 2 * (c + 1) * n ∧
              (∀ a, a ≠ 6 → a ≠ 14 → (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).natMem a = M6 a) ∧
              (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).realMem = R6 := by
            refine ⟨5, by omega, ?_⟩
            rw [show (5 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 from rfl]
            rw [run_succ, step_at' p q 41 _ _ _ _ (by omega) c41, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, m6, m0, m14, m24, m2, b1, hle] <;> first | trivial | omega)]
            rw [run_succ, step_at' p q 42 _ _ _ _ (by omega) c42, ex_rbrt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, m6, m0, m14, m24, m2, b1, hle] <;> first | trivial | assumption | linarith)]
            rw [run_succ, step_at' p q 47 _ _ _ _ (by omega) c47, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, m6, m0, m14, m24, m2, b1, hle] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p q 48 _ _ _ _ (by omega) c48, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, m6, m0, m14, m24, m2, b1, hle] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p q 49 _ _ _ _ (by omega) c49, ex_jump]
            rw [run_zero]
            try rfl
            refine ⟨rfl, ?_, ?_, ?_, rfl⟩
            all_goals first
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, m6, m0, m14, m24, m2]; done)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, m6, m0, m14, m24, m2]; ring1)
              | (intro a a6 a14; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, a6, a14])
          obtain ⟨τt, hτt, t1, t6, t14, tfr, tr⟩ := tl
          have e20 := tfr 20 (by omega) (by omega)
          have e22 := tfr 22 (by omega) (by omega)
          refine ⟨τt, hτt, t1, t6, t14, Or.inr ⟨?_, ?_, ?_, fun c' hc' => ?_⟩,
            fun a a6 a14 _ _ => tfr a a6 a14, fun a _ => by rw [tr]⟩
          · rw [e20, m20]; omega
          · rw [tr, e20, r4, hb4, m20]
          · rw [e22, e20, m20,
              m22, hb22]
          · rw [tr, r4]
            rcases Nat.lt_or_ge c' c with h | h
            · exact hball c' h
            · have : c' = c := by omega
              subst this; rw [← racc, ← r4]; exact hle
        · have b2 := hle
          have tl : ∃ τt, τt ≤ 9 ∧ (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).pc = q + 24 ∧ (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).natMem 6 = c + 1 ∧ (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).natMem 14 = B0 + 2 * (c + 1) * n ∧
          (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).natMem 20 = c ∧ (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).natMem 22 = B0 + 2 * c * n ∧ (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).realMem 4 = R6 2 ∧
          (∀ a, a ≠ 6 → a ≠ 14 → a ≠ 20 → a ≠ 22 → (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).natMem a = M6 a) ∧
          (∀ a, a ≠ 4 → (planarRAMRun p ⟨q + 41, M6, R6⟩ τt).realMem a = R6 a) := by
            refine ⟨9, by omega, ?_⟩
            rw [show (9 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
            rw [run_succ, step_at' p q 41 _ _ _ _ (by omega) c41, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, m6, m0, m14, m24, m2, b1, b2] <;> first | trivial | omega)]
            rw [run_succ, step_at' p q 42 _ _ _ _ (by omega) c42, ex_rbrf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, m6, m0, m14, m24, m2, b1, b2] <;> first | trivial | assumption | linarith)]
            rw [run_succ, step_at' p q 43 _ _ _ _ (by omega) c43, ex_rzero]
            rw [run_succ, step_at' p q 44 _ _ _ _ (by omega) c44, ex_radd _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, m6, m0, m14, m24, m2, b1, b2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p q 45 _ _ _ _ (by omega) c45, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, m6, m0, m14, m24, m2, b1, b2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p q 46 _ _ _ _ (by omega) c46, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, m6, m0, m14, m24, m2, b1, b2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p q 47 _ _ _ _ (by omega) c47, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, m6, m0, m14, m24, m2, b1, b2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p q 48 _ _ _ _ (by omega) c48, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, m6, m0, m14, m24, m2, b1, b2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p q 49 _ _ _ _ (by omega) c49, ex_jump]
            rw [run_zero]
            try rfl
            refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            all_goals first
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, m6, m0, m14, m24, m2, b1, b2]; done)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, m6, m0, m14, m24, m2, b1, b2] <;> omega)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, m6, m0, m14, m24, m2, b1, b2]; ring1)
              | (intro a a6 a14 a20 a22; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, a6, a14, a20, a22])
              | (intro a a4; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, a4])
          obtain ⟨τt, hτt, t1, t6, t14, t20, t22, t4, tfr, tRfr⟩ := tl
          refine ⟨τt, hτt, t1, t6, t14, Or.inr ⟨by omega, ?_, ?_, fun c' hc' => ?_⟩, tfr, tRfr⟩
          · rw [t4, t20, racc]
          · rw [t22, t20]
          · rw [t4]
            rcases Nat.lt_or_ge c' c with h | h
            · have := hball c' h
              rw [r4] at hle
              linarith
            · have : c' = c := by omega
              subst this; rw [racc]
    obtain ⟨τt, hτt, t1, t6, t14, tinv, tfr, tRfr⟩ := tl3
    set S7 := planarRAMRun p ⟨q + 41, M6, R6⟩ τt with hS7
    obtain ⟨pc7, M7, R7⟩ := S7
    simp only at t1 t6 t14 tinv tfr tRfr
    subst t1
    have m7 : ∀ a, a ≠ 6 → a ≠ 8 → a ≠ 10 → a ≠ 12 → a ≠ 14 → a ≠ 16 → a ≠ 20 → a ≠ 22 → M7 a = M a :=
      fun a a6 a8 a10 a12 a14 a16 a20 a22 => by rw [tfr a a6 a14 a20 a22, mm a a6 a8 a10 a12 a14 a16 a20 a22]
    have r7 : ∀ a, 6 ≤ a → R7 a = R a := fun a ha => by
      rw [tRfr a (by omega), vRfr a (by omega) (by omega), aRfr a (by omega)]
    obtain ⟨τ2, hτ2, r1, rinv, rfr, rRfr⟩ := ih (c + 1) M7 R7 (by omega)
      (fun a ha => by rw [m7 a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), hD a ha])
      (fun a ha => by rw [r7 a ha, hRw a ha])
      (by rw [m7 34 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h34])
      t6 t14
      (by rw [m7 28 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h28])
      (by rw [m7 18 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h18])
      (by rw [m7 24 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h24])
      (by rw [m7 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h0])
      (by rw [m7 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h2])
      (by rw [m7 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h4])
      tinv
    have hm : (12 * n + 20) * (r + 1) = (12 * n + 20) * r + (12 * n + 20) := by ring
    have hτv' : τv ≤ 12 * n + 1 := by simpa using hτv
    refine ⟨5 + τv + τt + τ2, by omega, ?_⟩
    rw [run_add, run_add, run_add, ← hS5, ← hS6, ← hS7]
    refine ⟨r1, rinv, fun a a6 a8 a10 a12 a14 a16 a20 a22 => ?_, fun a ha => ?_⟩
    · rw [rfr a a6 a8 a10 a12 a14 a16 a20 a22, m7 a a6 a8 a10 a12 a14 a16 a20 a22]
    · rw [rRfr a ha, r7 a ha]


set_option maxHeartbeats 4000000 in
lemma mloopN (K V : ℕ) :
    ∀ (r i acc : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), i + r = K →
      M 34 = K → M 32 = V → M 2 = 1 → M 6 = i → M 26 = acc →
      ∃ τ, τ ≤ 4 * r + 1 ∧ (planarRAMRun p ⟨q + 7, M, R⟩ τ).pc = q + 11 ∧
        (planarRAMRun p ⟨q + 7, M, R⟩ τ).natMem 26 = acc + r * V ∧
        (∀ a, a ≠ 6 → a ≠ 26 → (planarRAMRun p ⟨q + 7, M, R⟩ τ).natMem a = M a) ∧
        (planarRAMRun p ⟨q + 7, M, R⟩ τ).realMem = R := by
  have c0 : p[q + 0]? = some (natConst 0 0) := by simpa using hcode 0 (by simp)
  have c1 : p[q + 1]? = some (natConst 2 1) := by simpa using hcode 1 (by simp)
  have c2 : p[q + 2]? = some (natConst 4 2) := by simpa using hcode 2 (by simp)
  have c3 : p[q + 3]? = some (natAdd 24 32 32) := by simpa using hcode 3 (by simp)
  have c4 : p[q + 4]? = some (natAdd 18 28 24) := by simpa using hcode 4 (by simp)
  have c5 : p[q + 5]? = some (natConst 26 0) := by simpa using hcode 5 (by simp)
  have c6 : p[q + 6]? = some (natConst 6 0) := by simpa using hcode 6 (by simp)
  have c7 : p[q + 7]? = some (natBranch 34 6 (q + 11) (q + 8)) := by simpa using hcode 7 (by simp)
  have c8 : p[q + 8]? = some (natAdd 26 26 32) := by simpa using hcode 8 (by simp)
  have c9 : p[q + 9]? = some (natAdd 6 6 2) := by simpa using hcode 9 (by simp)
  have c10 : p[q + 10]? = some (jump (q + 7)) := by simpa using hcode 10 (by simp)
  have c11 : p[q + 11]? = some (natConst 30 0) := by simpa using hcode 11 (by simp)
  have c12 : p[q + 12]? = some (natConst 6 0) := by simpa using hcode 12 (by simp)
  have c13 : p[q + 13]? = some (natBranch 26 6 (q + 17) (q + 14)) := by simpa using hcode 13 (by simp)
  have c14 : p[q + 14]? = some (natAdd 30 30 26) := by simpa using hcode 14 (by simp)
  have c15 : p[q + 15]? = some (natAdd 6 6 2) := by simpa using hcode 15 (by simp)
  have c16 : p[q + 16]? = some (jump (q + 13)) := by simpa using hcode 16 (by simp)
  have c17 : p[q + 17]? = some (natAdd 30 30 30) := by simpa using hcode 17 (by simp)
  have c18 : p[q + 18]? = some (natConst 8 5) := by simpa using hcode 18 (by simp)
  have c19 : p[q + 19]? = some (natAdd 14 30 8) := by simpa using hcode 19 (by simp)
  have c20 : p[q + 20]? = some (natConst 6 0) := by simpa using hcode 20 (by simp)
  have c21 : p[q + 21]? = some (natConst 20 0) := by simpa using hcode 21 (by simp)
  have c22 : p[q + 22]? = some (natAdd 22 14 0) := by simpa using hcode 22 (by simp)
  have c23 : p[q + 23]? = some (realZero 4) := by simpa using hcode 23 (by simp)
  have c24 : p[q + 24]? = some (natBranch 34 6 (q + 50) (q + 25)) := by simpa using hcode 24 (by simp)
  have c25 : p[q + 25]? = some (realZero 2) := by simpa using hcode 25 (by simp)
  have c26 : p[q + 26]? = some (natAdd 10 28 0) := by simpa using hcode 26 (by simp)
  have c27 : p[q + 27]? = some (natConst 16 32) := by simpa using hcode 27 (by simp)
  have c28 : p[q + 28]? = some (natAdd 12 14 0) := by simpa using hcode 28 (by simp)
  have c29 : p[q + 29]? = some (natBranch 18 10 (q + 41) (q + 30)) := by simpa using hcode 29 (by simp)
  have c30 : p[q + 30]? = some (natLoad 8 12) := by simpa using hcode 30 (by simp)
  have c31 : p[q + 31]? = some (natBranch 2 8 (q + 32) (q + 37)) := by simpa using hcode 31 (by simp)
  have c32 : p[q + 32]? = some (natLoad 8 10) := by simpa using hcode 32 (by simp)
  have c33 : p[q + 33]? = some (natBranch 8 6 (q + 34) (q + 35)) := by simpa using hcode 33 (by simp)
  have c34 : p[q + 34]? = some (natBranch 6 8 (q + 37) (q + 35)) := by simpa using hcode 34 (by simp)
  have c35 : p[q + 35]? = some (realLoad 0 16) := by simpa using hcode 35 (by simp)
  have c36 : p[q + 36]? = some (realAdd 2 2 0) := by simpa using hcode 36 (by simp)
  have c37 : p[q + 37]? = some (natAdd 10 10 4) := by simpa using hcode 37 (by simp)
  have c38 : p[q + 38]? = some (natAdd 12 12 4) := by simpa using hcode 38 (by simp)
  have c39 : p[q + 39]? = some (natAdd 16 16 4) := by simpa using hcode 39 (by simp)
  have c40 : p[q + 40]? = some (jump (q + 29)) := by simpa using hcode 40 (by simp)
  have c41 : p[q + 41]? = some (natBranch 6 0 (q + 43) (q + 42)) := by simpa using hcode 41 (by simp)
  have c42 : p[q + 42]? = some (realBranch 2 4 (q + 47) (q + 43)) := by simpa using hcode 42 (by simp)
  have c43 : p[q + 43]? = some (realZero 4) := by simpa using hcode 43 (by simp)
  have c44 : p[q + 44]? = some (realAdd 4 4 2) := by simpa using hcode 44 (by simp)
  have c45 : p[q + 45]? = some (natAdd 20 6 0) := by simpa using hcode 45 (by simp)
  have c46 : p[q + 46]? = some (natAdd 22 14 0) := by simpa using hcode 46 (by simp)
  have c47 : p[q + 47]? = some (natAdd 14 14 24) := by simpa using hcode 47 (by simp)
  have c48 : p[q + 48]? = some (natAdd 6 6 2) := by simpa using hcode 48 (by simp)
  have c49 : p[q + 49]? = some (jump (q + 24)) := by simpa using hcode 49 (by simp)
  intro r
  induction r with
  | zero =>
    intro i acc M R hi hL hX h2 h6 hA
    refine ⟨1, by omega, ?_⟩
    rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_at p q 7 _ rfl c7, run_zero]
    simp only [execInstr, show M 34 ≤ M 6 by omega, if_true]
    exact ⟨trivial, by simp [hA], fun a _ _ => trivial, trivial⟩
  | succ r ih =>
    intro i acc M R hi hL hX h2 h6 hA
    have hlt : ¬ M 34 ≤ M 6 := by omega
    obtain ⟨τ2, hτ2, r1, rA, rfr, rr⟩ := ih (i + 1) (acc + V)
      (Function.update (Function.update M 26 (acc + V)) 6 (i + 1)) R (by omega)
      (by simp [Function.update_apply, hL]) (by simp [Function.update_apply, hX])
      (by simp [Function.update_apply, h2]) (by simp) (by simp [Function.update_apply])
    refine ⟨4 + τ2, by omega, ?_⟩
    have e4 : planarRAMRun p ⟨q + 7, M, R⟩ 4 =
        ⟨q + 7, Function.update (Function.update M 26 (acc + V)) 6 (i + 1), R⟩ := by
      rw [show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 from rfl, run_succ, step_at' p q 7 _ _ _ _ (by omega) c7,
        ex_brf _ _ _ _ _ _ _ hlt, run_succ, step_at' p q 8 _ _ _ _ (by omega) c8,
        ex_add _ _ _ _ _ _ _ (by rw [hA, hX]), run_succ, step_at' p q 9 _ _ _ _ (by omega) c9,
        ex_add _ _ _ _ _ _ _ (by simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte, h6, h2]; rfl),
        run_succ, step_at' p q 10 _ _ _ _ (by omega) c10, ex_jump, run_zero]
    rw [run_add, e4]
    refine ⟨r1, by rw [rA]; ring, fun a a6 aA => ?_, rr⟩
    rw [rfr a a6 aA, Function.update_of_ne a6, Function.update_of_ne aA]

set_option maxHeartbeats 4000000 in
lemma mloopNN (K V : ℕ) :
    ∀ (r i acc : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), i + r = K →
      M 26 = K → M 26 = V → M 2 = 1 → M 6 = i → M 30 = acc →
      ∃ τ, τ ≤ 4 * r + 1 ∧ (planarRAMRun p ⟨q + 13, M, R⟩ τ).pc = q + 17 ∧
        (planarRAMRun p ⟨q + 13, M, R⟩ τ).natMem 30 = acc + r * V ∧
        (∀ a, a ≠ 6 → a ≠ 30 → (planarRAMRun p ⟨q + 13, M, R⟩ τ).natMem a = M a) ∧
        (planarRAMRun p ⟨q + 13, M, R⟩ τ).realMem = R := by
  have c0 : p[q + 0]? = some (natConst 0 0) := by simpa using hcode 0 (by simp)
  have c1 : p[q + 1]? = some (natConst 2 1) := by simpa using hcode 1 (by simp)
  have c2 : p[q + 2]? = some (natConst 4 2) := by simpa using hcode 2 (by simp)
  have c3 : p[q + 3]? = some (natAdd 24 32 32) := by simpa using hcode 3 (by simp)
  have c4 : p[q + 4]? = some (natAdd 18 28 24) := by simpa using hcode 4 (by simp)
  have c5 : p[q + 5]? = some (natConst 26 0) := by simpa using hcode 5 (by simp)
  have c6 : p[q + 6]? = some (natConst 6 0) := by simpa using hcode 6 (by simp)
  have c7 : p[q + 7]? = some (natBranch 34 6 (q + 11) (q + 8)) := by simpa using hcode 7 (by simp)
  have c8 : p[q + 8]? = some (natAdd 26 26 32) := by simpa using hcode 8 (by simp)
  have c9 : p[q + 9]? = some (natAdd 6 6 2) := by simpa using hcode 9 (by simp)
  have c10 : p[q + 10]? = some (jump (q + 7)) := by simpa using hcode 10 (by simp)
  have c11 : p[q + 11]? = some (natConst 30 0) := by simpa using hcode 11 (by simp)
  have c12 : p[q + 12]? = some (natConst 6 0) := by simpa using hcode 12 (by simp)
  have c13 : p[q + 13]? = some (natBranch 26 6 (q + 17) (q + 14)) := by simpa using hcode 13 (by simp)
  have c14 : p[q + 14]? = some (natAdd 30 30 26) := by simpa using hcode 14 (by simp)
  have c15 : p[q + 15]? = some (natAdd 6 6 2) := by simpa using hcode 15 (by simp)
  have c16 : p[q + 16]? = some (jump (q + 13)) := by simpa using hcode 16 (by simp)
  have c17 : p[q + 17]? = some (natAdd 30 30 30) := by simpa using hcode 17 (by simp)
  have c18 : p[q + 18]? = some (natConst 8 5) := by simpa using hcode 18 (by simp)
  have c19 : p[q + 19]? = some (natAdd 14 30 8) := by simpa using hcode 19 (by simp)
  have c20 : p[q + 20]? = some (natConst 6 0) := by simpa using hcode 20 (by simp)
  have c21 : p[q + 21]? = some (natConst 20 0) := by simpa using hcode 21 (by simp)
  have c22 : p[q + 22]? = some (natAdd 22 14 0) := by simpa using hcode 22 (by simp)
  have c23 : p[q + 23]? = some (realZero 4) := by simpa using hcode 23 (by simp)
  have c24 : p[q + 24]? = some (natBranch 34 6 (q + 50) (q + 25)) := by simpa using hcode 24 (by simp)
  have c25 : p[q + 25]? = some (realZero 2) := by simpa using hcode 25 (by simp)
  have c26 : p[q + 26]? = some (natAdd 10 28 0) := by simpa using hcode 26 (by simp)
  have c27 : p[q + 27]? = some (natConst 16 32) := by simpa using hcode 27 (by simp)
  have c28 : p[q + 28]? = some (natAdd 12 14 0) := by simpa using hcode 28 (by simp)
  have c29 : p[q + 29]? = some (natBranch 18 10 (q + 41) (q + 30)) := by simpa using hcode 29 (by simp)
  have c30 : p[q + 30]? = some (natLoad 8 12) := by simpa using hcode 30 (by simp)
  have c31 : p[q + 31]? = some (natBranch 2 8 (q + 32) (q + 37)) := by simpa using hcode 31 (by simp)
  have c32 : p[q + 32]? = some (natLoad 8 10) := by simpa using hcode 32 (by simp)
  have c33 : p[q + 33]? = some (natBranch 8 6 (q + 34) (q + 35)) := by simpa using hcode 33 (by simp)
  have c34 : p[q + 34]? = some (natBranch 6 8 (q + 37) (q + 35)) := by simpa using hcode 34 (by simp)
  have c35 : p[q + 35]? = some (realLoad 0 16) := by simpa using hcode 35 (by simp)
  have c36 : p[q + 36]? = some (realAdd 2 2 0) := by simpa using hcode 36 (by simp)
  have c37 : p[q + 37]? = some (natAdd 10 10 4) := by simpa using hcode 37 (by simp)
  have c38 : p[q + 38]? = some (natAdd 12 12 4) := by simpa using hcode 38 (by simp)
  have c39 : p[q + 39]? = some (natAdd 16 16 4) := by simpa using hcode 39 (by simp)
  have c40 : p[q + 40]? = some (jump (q + 29)) := by simpa using hcode 40 (by simp)
  have c41 : p[q + 41]? = some (natBranch 6 0 (q + 43) (q + 42)) := by simpa using hcode 41 (by simp)
  have c42 : p[q + 42]? = some (realBranch 2 4 (q + 47) (q + 43)) := by simpa using hcode 42 (by simp)
  have c43 : p[q + 43]? = some (realZero 4) := by simpa using hcode 43 (by simp)
  have c44 : p[q + 44]? = some (realAdd 4 4 2) := by simpa using hcode 44 (by simp)
  have c45 : p[q + 45]? = some (natAdd 20 6 0) := by simpa using hcode 45 (by simp)
  have c46 : p[q + 46]? = some (natAdd 22 14 0) := by simpa using hcode 46 (by simp)
  have c47 : p[q + 47]? = some (natAdd 14 14 24) := by simpa using hcode 47 (by simp)
  have c48 : p[q + 48]? = some (natAdd 6 6 2) := by simpa using hcode 48 (by simp)
  have c49 : p[q + 49]? = some (jump (q + 24)) := by simpa using hcode 49 (by simp)
  intro r
  induction r with
  | zero =>
    intro i acc M R hi hL hX h2 h6 hA
    refine ⟨1, by omega, ?_⟩
    rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_at p q 13 _ rfl c13, run_zero]
    simp only [execInstr, show M 26 ≤ M 6 by omega, if_true]
    exact ⟨trivial, by simp [hA], fun a _ _ => trivial, trivial⟩
  | succ r ih =>
    intro i acc M R hi hL hX h2 h6 hA
    have hlt : ¬ M 26 ≤ M 6 := by omega
    obtain ⟨τ2, hτ2, r1, rA, rfr, rr⟩ := ih (i + 1) (acc + V)
      (Function.update (Function.update M 30 (acc + V)) 6 (i + 1)) R (by omega)
      (by simp [Function.update_apply, hL]) (by simp [Function.update_apply, hX])
      (by simp [Function.update_apply, h2]) (by simp) (by simp [Function.update_apply])
    refine ⟨4 + τ2, by omega, ?_⟩
    have e4 : planarRAMRun p ⟨q + 13, M, R⟩ 4 =
        ⟨q + 13, Function.update (Function.update M 30 (acc + V)) 6 (i + 1), R⟩ := by
      rw [show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 from rfl, run_succ, step_at' p q 13 _ _ _ _ (by omega) c13,
        ex_brf _ _ _ _ _ _ _ hlt, run_succ, step_at' p q 14 _ _ _ _ (by omega) c14,
        ex_add _ _ _ _ _ _ _ (by rw [hA, hX]), run_succ, step_at' p q 15 _ _ _ _ (by omega) c15,
        ex_add _ _ _ _ _ _ _ (by simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte, h6, h2]; rfl),
        run_succ, step_at' p q 16 _ _ _ _ (by omega) c16, ex_jump, run_zero]
    rw [run_add, e4]
    refine ⟨r1, by rw [rA]; ring, fun a a6 aA => ?_, rr⟩
    rw [rfr a a6 aA, Function.update_of_ne a6, Function.update_of_ne aA]

set_option maxHeartbeats 16000000 in
lemma best_select (n k LVB : ℕ) (hk : 0 < k) (hLe : LVB % 2 = 0) (hL : 40 ≤ LVB)
    (M : ℕ → ℕ) (R : ℕ → ℝ) (h32 : M 32 = n) (h34 : M 34 = k) (h28 : M 28 = LVB) :
    ∃ τ, τ ≤ (16 * n + 24) * k + 20 ∧ (planarRAMRun p ⟨q, M, R⟩ τ).pc = q + 50 ∧ (planarRAMRun p ⟨q, M, R⟩ τ).natMem 20 < k ∧
      (planarRAMRun p ⟨q, M, R⟩ τ).natMem 22 = 5 + 2 * (k * n) * (k * n) + 2 * (planarRAMRun p ⟨q, M, R⟩ τ).natMem 20 * n ∧
      (∀ c', c' < k → (∑ j ∈ Finset.range n, if 1 ≤ M (5 + 2 * (k * n) * (k * n) + 2 * c' * n + 2 * j) ∧ M (LVB + 2 * j) ≠ c' then R (32 + 2 * j) else 0) ≤ (∑ j ∈ Finset.range n, if 1 ≤ M (5 + 2 * (k * n) * (k * n) + 2 * (planarRAMRun p ⟨q, M, R⟩ τ).natMem 20 * n + 2 * j) ∧ M (LVB + 2 * j) ≠ (planarRAMRun p ⟨q, M, R⟩ τ).natMem 20 then R (32 + 2 * j) else 0)) ∧
      (∀ a, (a % 2 = 1 ∨ 40 ≤ a) → (planarRAMRun p ⟨q, M, R⟩ τ).natMem a = M a) ∧
      (∀ a, 6 ≤ a → (planarRAMRun p ⟨q, M, R⟩ τ).realMem a = R a) := by
  have c0 : p[q + 0]? = some (natConst 0 0) := by simpa using hcode 0 (by simp)
  have c1 : p[q + 1]? = some (natConst 2 1) := by simpa using hcode 1 (by simp)
  have c2 : p[q + 2]? = some (natConst 4 2) := by simpa using hcode 2 (by simp)
  have c3 : p[q + 3]? = some (natAdd 24 32 32) := by simpa using hcode 3 (by simp)
  have c4 : p[q + 4]? = some (natAdd 18 28 24) := by simpa using hcode 4 (by simp)
  have c5 : p[q + 5]? = some (natConst 26 0) := by simpa using hcode 5 (by simp)
  have c6 : p[q + 6]? = some (natConst 6 0) := by simpa using hcode 6 (by simp)
  have c7 : p[q + 7]? = some (natBranch 34 6 (q + 11) (q + 8)) := by simpa using hcode 7 (by simp)
  have c8 : p[q + 8]? = some (natAdd 26 26 32) := by simpa using hcode 8 (by simp)
  have c9 : p[q + 9]? = some (natAdd 6 6 2) := by simpa using hcode 9 (by simp)
  have c10 : p[q + 10]? = some (jump (q + 7)) := by simpa using hcode 10 (by simp)
  have c11 : p[q + 11]? = some (natConst 30 0) := by simpa using hcode 11 (by simp)
  have c12 : p[q + 12]? = some (natConst 6 0) := by simpa using hcode 12 (by simp)
  have c13 : p[q + 13]? = some (natBranch 26 6 (q + 17) (q + 14)) := by simpa using hcode 13 (by simp)
  have c14 : p[q + 14]? = some (natAdd 30 30 26) := by simpa using hcode 14 (by simp)
  have c15 : p[q + 15]? = some (natAdd 6 6 2) := by simpa using hcode 15 (by simp)
  have c16 : p[q + 16]? = some (jump (q + 13)) := by simpa using hcode 16 (by simp)
  have c17 : p[q + 17]? = some (natAdd 30 30 30) := by simpa using hcode 17 (by simp)
  have c18 : p[q + 18]? = some (natConst 8 5) := by simpa using hcode 18 (by simp)
  have c19 : p[q + 19]? = some (natAdd 14 30 8) := by simpa using hcode 19 (by simp)
  have c20 : p[q + 20]? = some (natConst 6 0) := by simpa using hcode 20 (by simp)
  have c21 : p[q + 21]? = some (natConst 20 0) := by simpa using hcode 21 (by simp)
  have c22 : p[q + 22]? = some (natAdd 22 14 0) := by simpa using hcode 22 (by simp)
  have c23 : p[q + 23]? = some (realZero 4) := by simpa using hcode 23 (by simp)
  have c24 : p[q + 24]? = some (natBranch 34 6 (q + 50) (q + 25)) := by simpa using hcode 24 (by simp)
  have c25 : p[q + 25]? = some (realZero 2) := by simpa using hcode 25 (by simp)
  have c26 : p[q + 26]? = some (natAdd 10 28 0) := by simpa using hcode 26 (by simp)
  have c27 : p[q + 27]? = some (natConst 16 32) := by simpa using hcode 27 (by simp)
  have c28 : p[q + 28]? = some (natAdd 12 14 0) := by simpa using hcode 28 (by simp)
  have c29 : p[q + 29]? = some (natBranch 18 10 (q + 41) (q + 30)) := by simpa using hcode 29 (by simp)
  have c30 : p[q + 30]? = some (natLoad 8 12) := by simpa using hcode 30 (by simp)
  have c31 : p[q + 31]? = some (natBranch 2 8 (q + 32) (q + 37)) := by simpa using hcode 31 (by simp)
  have c32 : p[q + 32]? = some (natLoad 8 10) := by simpa using hcode 32 (by simp)
  have c33 : p[q + 33]? = some (natBranch 8 6 (q + 34) (q + 35)) := by simpa using hcode 33 (by simp)
  have c34 : p[q + 34]? = some (natBranch 6 8 (q + 37) (q + 35)) := by simpa using hcode 34 (by simp)
  have c35 : p[q + 35]? = some (realLoad 0 16) := by simpa using hcode 35 (by simp)
  have c36 : p[q + 36]? = some (realAdd 2 2 0) := by simpa using hcode 36 (by simp)
  have c37 : p[q + 37]? = some (natAdd 10 10 4) := by simpa using hcode 37 (by simp)
  have c38 : p[q + 38]? = some (natAdd 12 12 4) := by simpa using hcode 38 (by simp)
  have c39 : p[q + 39]? = some (natAdd 16 16 4) := by simpa using hcode 39 (by simp)
  have c40 : p[q + 40]? = some (jump (q + 29)) := by simpa using hcode 40 (by simp)
  have c41 : p[q + 41]? = some (natBranch 6 0 (q + 43) (q + 42)) := by simpa using hcode 41 (by simp)
  have c42 : p[q + 42]? = some (realBranch 2 4 (q + 47) (q + 43)) := by simpa using hcode 42 (by simp)
  have c43 : p[q + 43]? = some (realZero 4) := by simpa using hcode 43 (by simp)
  have c44 : p[q + 44]? = some (realAdd 4 4 2) := by simpa using hcode 44 (by simp)
  have c45 : p[q + 45]? = some (natAdd 20 6 0) := by simpa using hcode 45 (by simp)
  have c46 : p[q + 46]? = some (natAdd 22 14 0) := by simpa using hcode 46 (by simp)
  have c47 : p[q + 47]? = some (natAdd 14 14 24) := by simpa using hcode 47 (by simp)
  have c48 : p[q + 48]? = some (natAdd 6 6 2) := by simpa using hcode 48 (by simp)
  have c49 : p[q + 49]? = some (jump (q + 24)) := by simpa using hcode 49 (by simp)
  have sA : (planarRAMRun p ⟨q, M, R⟩ 7).pc = q + 7 ∧ (planarRAMRun p ⟨q, M, R⟩ 7).natMem 0 = 0 ∧ (planarRAMRun p ⟨q, M, R⟩ 7).natMem 2 = 1 ∧ (planarRAMRun p ⟨q, M, R⟩ 7).natMem 4 = 2 ∧
      (planarRAMRun p ⟨q, M, R⟩ 7).natMem 24 = 2 * n ∧ (planarRAMRun p ⟨q, M, R⟩ 7).natMem 18 = LVB + 2 * n ∧ (planarRAMRun p ⟨q, M, R⟩ 7).natMem 26 = 0 ∧ (planarRAMRun p ⟨q, M, R⟩ 7).natMem 6 = 0 ∧
      (∀ a, a ≠ 0 → a ≠ 2 → a ≠ 4 → a ≠ 24 → a ≠ 18 → a ≠ 26 → a ≠ 6 → (planarRAMRun p ⟨q, M, R⟩ 7).natMem a = M a) ∧ (planarRAMRun p ⟨q, M, R⟩ 7).realMem = R := by
    rw [show (7 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
    rw [run_succ, step_at' p q 0 _ _ _ _ (by omega) c0, ex_const]
    rw [run_succ, step_at' p q 1 _ _ _ _ (by omega) c1, ex_const]
    rw [run_succ, step_at' p q 2 _ _ _ _ (by omega) c2, ex_const]
    rw [run_succ, step_at' p q 3 _ _ _ _ (by omega) c3, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h32, h34, h28] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p q 4 _ _ _ _ (by omega) c4, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h32, h34, h28] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p q 5 _ _ _ _ (by omega) c5, ex_const]
    rw [run_succ, step_at' p q 6 _ _ _ _ (by omega) c6, ex_const]
    rw [run_zero]
    try rfl
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    all_goals first
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h32, h34, h28]; done)
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h32, h34, h28] <;> omega)
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h32, h34, h28]; ring1)
      | (intro a a0 a2 a4 a24 a18 a26 a6; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, a0, a2, a4, a24, a18, a26, a6])
      | (intro a a4; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, a4])
  obtain ⟨a1, a0, a2, a4, a24, a18, a26, a6, afr, ar⟩ := sA
  set S7 := planarRAMRun p ⟨q, M, R⟩ 7 with hS7
  obtain ⟨pc7, M7, R7⟩ := S7
  simp only at a1 a0 a2 a4 a24 a18 a26 a6 afr ar
  subst a1; subst R7
  have f7 : ∀ a, 28 ≤ a → M7 a = M a := fun a ha => afr a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨τ1, hτ1, l1, l26, lfr, lr⟩ := mloopN p q hcode k n k 0 0 M7 R (by omega)
    (by rw [f7 34 (by omega), h34]) (by rw [f7 32 (by omega), h32]) a2 a6 a26
  set S8 := planarRAMRun p ⟨q + 7, M7, R⟩ τ1 with hS8
  obtain ⟨pc8, M1, R8⟩ := S8
  simp only at l1 l26 lfr lr
  subst l1; subst R8
  have g26 : M1 26 = k * n := by rw [l26]; ring
  have sB : (planarRAMRun p ⟨q + 11, M1, R⟩ 2).pc = q + 13 ∧ (planarRAMRun p ⟨q + 11, M1, R⟩ 2).natMem 30 = 0 ∧ (planarRAMRun p ⟨q + 11, M1, R⟩ 2).natMem 6 = 0 ∧
      (∀ a, a ≠ 30 → a ≠ 6 → (planarRAMRun p ⟨q + 11, M1, R⟩ 2).natMem a = M1 a) ∧ (planarRAMRun p ⟨q + 11, M1, R⟩ 2).realMem = R := by
    rw [show (2 : ℕ) = 0 + 1 + 1 from rfl]
    rw [run_succ, step_at' p q 11 _ _ _ _ (by omega) c11, ex_const]
    rw [run_succ, step_at' p q 12 _ _ _ _ (by omega) c12, ex_const]
    rw [run_zero]
    try rfl
    refine ⟨rfl, ?_, ?_, ?_, rfl⟩
    all_goals first
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, g26]; done)
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, g26] <;> omega)
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, g26]; ring1)
      | (intro a a30 a6; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, a30, a6])
      | (intro a a4; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, a4])
  obtain ⟨b1, b30, b6, bfr, br⟩ := sB
  set S9 := planarRAMRun p ⟨q + 11, M1, R⟩ 2 with hS9
  obtain ⟨pc9, M9, R9⟩ := S9
  simp only at b1 b30 b6 bfr br
  subst b1; subst R9
  obtain ⟨τ2, hτ2, n1, n30, nfr, nr⟩ := mloopNN p q hcode (k * n) (k * n) (k * n) 0 0 M9 R (by omega)
    (by rw [bfr 26 (by omega) (by omega), g26]) (by rw [bfr 26 (by omega) (by omega), g26])
    (by rw [bfr 2 (by omega) (by omega), lfr 2 (by omega) (by omega), a2]) b6 b30
  set S10 := planarRAMRun p ⟨q + 13, M9, R⟩ τ2 with hS10
  obtain ⟨pc10, M2, R10⟩ := S10
  simp only at n1 n30 nfr nr
  subst n1; subst R10
  have g30 : M2 30 = (k * n) * (k * n) := by rw [n30]; ring
  have g0 : M2 0 = 0 := by rw [nfr 0 (by omega) (by omega), bfr 0 (by omega) (by omega), lfr 0 (by omega) (by omega), a0]
  have sC : (planarRAMRun p ⟨q + 17, M2, R⟩ 7).pc = q + 24 ∧ (planarRAMRun p ⟨q + 17, M2, R⟩ 7).natMem 14 = 5 + 2 * (k * n) * (k * n) + 2 * 0 * n ∧ (planarRAMRun p ⟨q + 17, M2, R⟩ 7).natMem 6 = 0 ∧
      (planarRAMRun p ⟨q + 17, M2, R⟩ 7).natMem 20 = 0 ∧ (planarRAMRun p ⟨q + 17, M2, R⟩ 7).natMem 22 = 5 + 2 * (k * n) * (k * n) + 2 * 0 * n ∧
      (∀ a, a ≠ 30 → a ≠ 8 → a ≠ 14 → a ≠ 6 → a ≠ 20 → a ≠ 22 → (planarRAMRun p ⟨q + 17, M2, R⟩ 7).natMem a = M2 a) ∧ (∀ a, a ≠ 4 → (planarRAMRun p ⟨q + 17, M2, R⟩ 7).realMem a = R a) := by
    rw [show (7 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
    rw [run_succ, step_at' p q 17 _ _ _ _ (by omega) c17, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g30, g0] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p q 18 _ _ _ _ (by omega) c18, ex_const]
    rw [run_succ, step_at' p q 19 _ _ _ _ (by omega) c19, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g30, g0] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p q 20 _ _ _ _ (by omega) c20, ex_const]
    rw [run_succ, step_at' p q 21 _ _ _ _ (by omega) c21, ex_const]
    rw [run_succ, step_at' p q 22 _ _ _ _ (by omega) c22, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g30, g0] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p q 23 _ _ _ _ (by omega) c23, ex_rzero]
    rw [run_zero]
    try rfl
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, g30, g0]; done)
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, g30, g0] <;> omega)
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, g30, g0]; ring1)
      | (intro a a30 a8 a14 a6 a20 a22; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, a30, a8, a14, a6, a20, a22])
      | (intro a a4; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, a4])
  obtain ⟨c1, c14, c6, c20, c22, cfr, cRfr⟩ := sC
  set S11 := planarRAMRun p ⟨q + 17, M2, R⟩ 7 with hS11
  obtain ⟨pc11, M3, R3⟩ := S11
  simp only at c1 c14 c6 c20 c22 cfr cRfr
  subst c1
  have e3 : ∀ a, a ≠ 0 → a ≠ 2 → a ≠ 4 → a ≠ 24 → a ≠ 18 → a ≠ 26 → a ≠ 6 → a ≠ 30 → a ≠ 8 → a ≠ 14 →
      a ≠ 20 → a ≠ 22 → M3 a = M a := fun a a0 a2 a4 a24 a18 a26 a6 a30 a8 a14 a20 a22 => by
    rw [cfr a a30 a8 a14 a6 a20 a22, nfr a a6 a30, bfr a a30 a6, lfr a a6 a26, afr a a0 a2 a4 a24 a18 a26 a6]
  have hB0 : (5 + 2 * (k * n) * (k * n)) % 2 = 1 := by
    have e : 2 * (k * n) * (k * n) = 2 * ((k * n) * (k * n)) := by ring
    omega
  have k3 : ∀ a, a ≠ 30 → a ≠ 8 → a ≠ 14 → a ≠ 6 → a ≠ 20 → a ≠ 22 → M3 a = M2 a := cfr
  obtain ⟨τc, hτc, r1, rinv, rfr, rRfr⟩ := csel_loop p q hcode n k LVB (5 + 2 * (k * n) * (k * n)) M R hLe hL hB0
    k 0 M3 R3 (by omega)
    (fun a ha => e3 a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega))
    (fun a ha => cRfr a (by omega))
    (by rw [e3 34 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), h34]) c6 c14
    (by rw [e3 28 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), h28])
    (by rw [k3 18 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), nfr 18 (by omega) (by omega),
      bfr 18 (by omega) (by omega), lfr 18 (by omega) (by omega), a18])
    (by rw [k3 24 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), nfr 24 (by omega) (by omega),
      bfr 24 (by omega) (by omega), lfr 24 (by omega) (by omega), a24])
    (by rw [k3 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g0])
    (by rw [k3 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), nfr 2 (by omega) (by omega),
      bfr 2 (by omega) (by omega), lfr 2 (by omega) (by omega), a2])
    (by rw [k3 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), nfr 4 (by omega) (by omega),
      bfr 4 (by omega) (by omega), lfr 4 (by omega) (by omega), a4])
    (Or.inl rfl)
  obtain ⟨hb1, hb4, hb22, hball⟩ := rinv.resolve_left (by omega)
  have hk1 : (12 * n + 20) * k + 1 + (4 * (k * n) + 1) + (4 * k + 1) + 16 ≤ (16 * n + 24) * k + 20 := by
    have : (12 * n + 20) * k + 4 * (k * n) + 4 * k = (16 * n + 24) * k := by ring
    omega
  refine ⟨7 + τ1 + 2 + τ2 + 7 + τc, by omega, ?_⟩
  rw [run_add, run_add, run_add, run_add, run_add, ← hS7, ← hS8, ← hS9, ← hS10, ← hS11]
  refine ⟨r1, hb1, hb22, fun c' hc' => by rw [← hb4]; exact hball c' hc', fun a ha => ?_, fun a ha => ?_⟩
  · rw [rfr a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      e3 a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)]
  · rw [rRfr a ha, cRfr a (by omega)]

end

end BS

open WilliamsonShmoys PlanarRAMInstruction
open Classical in
theorem solution (p : List PlanarRAMInstruction) (q : ℕ)
    (hcode : CodeAt p q
    [natConst 0 0,
      natConst 2 1,
      natConst 4 2,
      natAdd 24 32 32,
      natAdd 18 28 24,
      natConst 26 0,
      natConst 6 0,
      natBranch 34 6 (q + 11) (q + 8),
      natAdd 26 26 32,
      natAdd 6 6 2,
      jump (q + 7),
      natConst 30 0,
      natConst 6 0,
      natBranch 26 6 (q + 17) (q + 14),
      natAdd 30 30 26,
      natAdd 6 6 2,
      jump (q + 13),
      natAdd 30 30 30,
      natConst 8 5,
      natAdd 14 30 8,
      natConst 6 0,
      natConst 20 0,
      natAdd 22 14 0,
      realZero 4,
      natBranch 34 6 (q + 50) (q + 25),
      realZero 2,
      natAdd 10 28 0,
      natConst 16 32,
      natAdd 12 14 0,
      natBranch 18 10 (q + 41) (q + 30),
      natLoad 8 12,
      natBranch 2 8 (q + 32) (q + 37),
      natLoad 8 10,
      natBranch 8 6 (q + 34) (q + 35),
      natBranch 6 8 (q + 37) (q + 35),
      realLoad 0 16,
      realAdd 2 2 0,
      natAdd 10 10 4,
      natAdd 12 12 4,
      natAdd 16 16 4,
      jump (q + 29),
      natBranch 6 0 (q + 43) (q + 42),
      realBranch 2 4 (q + 47) (q + 43),
      realZero 4,
      realAdd 4 4 2,
      natAdd 20 6 0,
      natAdd 22 14 0,
      natAdd 14 14 24,
      natAdd 6 6 2,
      jump (q + 24)])
    (n k LVB : ℕ) (hk : 0 < k) (hLe : LVB % 2 = 0) (hL : 40 ≤ LVB)
    (M : ℕ → ℕ) (R : ℕ → ℝ) (h32 : M 32 = n) (h34 : M 34 = k) (h28 : M 28 = LVB) :
    ∃ τ, τ ≤ (16 * n + 24) * k + 20 ∧ (planarRAMRun p ⟨q, M, R⟩ τ).pc = q + 50 ∧ (planarRAMRun p ⟨q, M, R⟩ τ).natMem 20 < k ∧
      (planarRAMRun p ⟨q, M, R⟩ τ).natMem 22 = 5 + 2 * (k * n) * (k * n) + 2 * (planarRAMRun p ⟨q, M, R⟩ τ).natMem 20 * n ∧
      (∀ c', c' < k → (∑ j ∈ Finset.range n, if 1 ≤ M (5 + 2 * (k * n) * (k * n) + 2 * c' * n + 2 * j) ∧ M (LVB + 2 * j) ≠ c' then R (32 + 2 * j) else 0) ≤ (∑ j ∈ Finset.range n, if 1 ≤ M (5 + 2 * (k * n) * (k * n) + 2 * (planarRAMRun p ⟨q, M, R⟩ τ).natMem 20 * n + 2 * j) ∧ M (LVB + 2 * j) ≠ (planarRAMRun p ⟨q, M, R⟩ τ).natMem 20 then R (32 + 2 * j) else 0)) ∧
      (∀ a, (a % 2 = 1 ∨ 40 ≤ a) → (planarRAMRun p ⟨q, M, R⟩ τ).natMem a = M a) ∧
      (∀ a, 6 ≤ a → (planarRAMRun p ⟨q, M, R⟩ τ).realMem a = R a) :=
  BS.best_select p q hcode n k LVB hk hLe hL M R h32 h34 h28
