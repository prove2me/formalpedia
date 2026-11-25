-- Prove2me | solution 1 for WilliamsonShmoys.ram_output_bitmap_write
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T08:34:55.797493+00:00
-- url     : https://prove2.me/submissions/c29f887a-5e9d-427d-82f9-cdc787bae1e4

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false

namespace OU
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
variable (p : List PlanarRAMInstruction) (o : ℕ)
  (hcode : CodeAt p o
    [natConst 0 0,
      natConst 2 1,
      natConst 4 2,
      natConst 36 16,
      natAdd 24 32 32,
      natAdd 18 28 24,
      natConst 30 0,
      natConst 6 0,
      natBranch 32 6 (o + 12) (o + 9),
      natAdd 30 30 32,
      natAdd 6 6 2,
      jump (o + 8),
      natAdd 26 30 0,
      natAdd 30 30 30,
      natAdd 30 30 30,
      natAdd 30 30 30,
      natAdd 30 30 30,
      natConst 8 32,
      natAdd 38 30 8,
      natAdd 10 28 0,
      natAdd 12 22 0,
      natBranch 18 10 (o + 34) (o + 22),
      natLoad 8 12,
      natBranch 2 8 (o + 24) (o + 29),
      natLoad 8 10,
      natBranch 8 20 (o + 26) (o + 27),
      natBranch 20 8 (o + 29) (o + 27),
      natStore 38 2,
      jump (o + 30),
      natStore 38 0,
      natAdd 10 10 4,
      natAdd 12 12 4,
      natAdd 38 38 36,
      jump (o + 21),
      natAdd 0 26 32,
      natAdd 0 0 2,
      natAdd 8 30 36,
      natStore 8 8,
      natAdd 1 0 0,
      natAdd 1 1 1,
      natAdd 1 1 1,
      natAdd 1 1 1,
      natLoad 1 1,
      natBranch 0 1 (o + 48) (o + 44),
      natStore 0 1,
      natConst 1 1,
      natSub 0 0 1,
      jump (o + 38)])
include hcode

set_option maxHeartbeats 8000000 in
lemma copy_loop (n : ℕ) (val : ℕ → ℕ) (hval : ∀ j, val j ≤ 1) :
    ∀ (r : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), r ≤ n →
      M 0 = n * n + 1 + r → (∀ j, j < r → M (16 * (n * n + 2 + j)) = val j) →
      M (16 * (n * n + 1)) = 16 * (n * n + 1) →
      ∃ τ, τ ≤ 10 * r + 6 ∧ (planarRAMRun p ⟨o + 38, M, R⟩ τ).pc = o + 48 ∧
        (∀ j, j < r → (planarRAMRun p ⟨o + 38, M, R⟩ τ).natMem (n * n + 2 + j) = val j) ∧
        (∀ a, a ≠ 0 → a ≠ 1 → (∀ j, j < r → a ≠ n * n + 2 + j) → (planarRAMRun p ⟨o + 38, M, R⟩ τ).natMem a = M a) ∧ (planarRAMRun p ⟨o + 38, M, R⟩ τ).realMem = R := by
  have c0 : p[o + 0]? = some (natConst 0 0) := by simpa using hcode 0 (by simp)
  have c1 : p[o + 1]? = some (natConst 2 1) := by simpa using hcode 1 (by simp)
  have c2 : p[o + 2]? = some (natConst 4 2) := by simpa using hcode 2 (by simp)
  have c3 : p[o + 3]? = some (natConst 36 16) := by simpa using hcode 3 (by simp)
  have c4 : p[o + 4]? = some (natAdd 24 32 32) := by simpa using hcode 4 (by simp)
  have c5 : p[o + 5]? = some (natAdd 18 28 24) := by simpa using hcode 5 (by simp)
  have c6 : p[o + 6]? = some (natConst 30 0) := by simpa using hcode 6 (by simp)
  have c7 : p[o + 7]? = some (natConst 6 0) := by simpa using hcode 7 (by simp)
  have c8 : p[o + 8]? = some (natBranch 32 6 (o + 12) (o + 9)) := by simpa using hcode 8 (by simp)
  have c9 : p[o + 9]? = some (natAdd 30 30 32) := by simpa using hcode 9 (by simp)
  have c10 : p[o + 10]? = some (natAdd 6 6 2) := by simpa using hcode 10 (by simp)
  have c11 : p[o + 11]? = some (jump (o + 8)) := by simpa using hcode 11 (by simp)
  have c12 : p[o + 12]? = some (natAdd 26 30 0) := by simpa using hcode 12 (by simp)
  have c13 : p[o + 13]? = some (natAdd 30 30 30) := by simpa using hcode 13 (by simp)
  have c14 : p[o + 14]? = some (natAdd 30 30 30) := by simpa using hcode 14 (by simp)
  have c15 : p[o + 15]? = some (natAdd 30 30 30) := by simpa using hcode 15 (by simp)
  have c16 : p[o + 16]? = some (natAdd 30 30 30) := by simpa using hcode 16 (by simp)
  have c17 : p[o + 17]? = some (natConst 8 32) := by simpa using hcode 17 (by simp)
  have c18 : p[o + 18]? = some (natAdd 38 30 8) := by simpa using hcode 18 (by simp)
  have c19 : p[o + 19]? = some (natAdd 10 28 0) := by simpa using hcode 19 (by simp)
  have c20 : p[o + 20]? = some (natAdd 12 22 0) := by simpa using hcode 20 (by simp)
  have c21 : p[o + 21]? = some (natBranch 18 10 (o + 34) (o + 22)) := by simpa using hcode 21 (by simp)
  have c22 : p[o + 22]? = some (natLoad 8 12) := by simpa using hcode 22 (by simp)
  have c23 : p[o + 23]? = some (natBranch 2 8 (o + 24) (o + 29)) := by simpa using hcode 23 (by simp)
  have c24 : p[o + 24]? = some (natLoad 8 10) := by simpa using hcode 24 (by simp)
  have c25 : p[o + 25]? = some (natBranch 8 20 (o + 26) (o + 27)) := by simpa using hcode 25 (by simp)
  have c26 : p[o + 26]? = some (natBranch 20 8 (o + 29) (o + 27)) := by simpa using hcode 26 (by simp)
  have c27 : p[o + 27]? = some (natStore 38 2) := by simpa using hcode 27 (by simp)
  have c28 : p[o + 28]? = some (jump (o + 30)) := by simpa using hcode 28 (by simp)
  have c29 : p[o + 29]? = some (natStore 38 0) := by simpa using hcode 29 (by simp)
  have c30 : p[o + 30]? = some (natAdd 10 10 4) := by simpa using hcode 30 (by simp)
  have c31 : p[o + 31]? = some (natAdd 12 12 4) := by simpa using hcode 31 (by simp)
  have c32 : p[o + 32]? = some (natAdd 38 38 36) := by simpa using hcode 32 (by simp)
  have c33 : p[o + 33]? = some (jump (o + 21)) := by simpa using hcode 33 (by simp)
  have c34 : p[o + 34]? = some (natAdd 0 26 32) := by simpa using hcode 34 (by simp)
  have c35 : p[o + 35]? = some (natAdd 0 0 2) := by simpa using hcode 35 (by simp)
  have c36 : p[o + 36]? = some (natAdd 8 30 36) := by simpa using hcode 36 (by simp)
  have c37 : p[o + 37]? = some (natStore 8 8) := by simpa using hcode 37 (by simp)
  have c38 : p[o + 38]? = some (natAdd 1 0 0) := by simpa using hcode 38 (by simp)
  have c39 : p[o + 39]? = some (natAdd 1 1 1) := by simpa using hcode 39 (by simp)
  have c40 : p[o + 40]? = some (natAdd 1 1 1) := by simpa using hcode 40 (by simp)
  have c41 : p[o + 41]? = some (natAdd 1 1 1) := by simpa using hcode 41 (by simp)
  have c42 : p[o + 42]? = some (natLoad 1 1) := by simpa using hcode 42 (by simp)
  have c43 : p[o + 43]? = some (natBranch 0 1 (o + 48) (o + 44)) := by simpa using hcode 43 (by simp)
  have c44 : p[o + 44]? = some (natStore 0 1) := by simpa using hcode 44 (by simp)
  have c45 : p[o + 45]? = some (natConst 1 1) := by simpa using hcode 45 (by simp)
  have c46 : p[o + 46]? = some (natSub 0 0 1) := by simpa using hcode 46 (by simp)
  have c47 : p[o + 47]? = some (jump (o + 38)) := by simpa using hcode 47 (by simp)
  intro r
  induction r with
  | zero =>
    intro M R hr h0 hT hS
    refine ⟨6, by omega, ?_⟩
    rw [show (6 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
    rw [run_succ, step_at' p o 38 _ _ _ _ (by omega) c38, ex_add _ _ _ _ (2 * (n * n + 1)) _ _ (by rw [h0]; ring)]
    rw [run_succ, step_at' p o 39 _ _ _ _ (by omega) c39, ex_add _ _ _ _ (4 * (n * n + 1)) _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false]; ring)]
    rw [run_succ, step_at' p o 40 _ _ _ _ (by omega) c40, ex_add _ _ _ _ (8 * (n * n + 1)) _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false]; ring)]
    rw [run_succ, step_at' p o 41 _ _ _ _ (by omega) c41, ex_add _ _ _ _ (16 * (n * n + 1)) _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false]; ring)]
    rw [run_succ, step_at' p o 42 _ _ _ _ (by omega) c42, ex_load _ _ _ (16 * (n * n + 1)) _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, show 16 * (n * n + 1) ≠ 1 by omega]; first | exact hS | exact hv)]
    rw [run_succ, step_at' p o 43 _ _ _ _ (by omega) c43, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h0]; omega), run_zero]
    exact ⟨rfl, fun j hj => by omega, fun a _ a1 _ => by simp only [Function.update_apply, a1, if_false], rfl⟩
  | succ r ih =>
    intro M R hr h0 hT hS
    have hv := hT r (by omega)
    have hvb := hval r
    have hd : M 0 = n * n + 2 + r := by omega
    obtain ⟨M1, e10, f0, fd, ffr⟩ : ∃ M1, planarRAMRun p ⟨o + 38, M, R⟩ 10 = ⟨o + 38, M1, R⟩ ∧
        M1 0 = n * n + 1 + r ∧ M1 (n * n + 2 + r) = val r ∧
        (∀ a, a ≠ 0 → a ≠ 1 → a ≠ n * n + 2 + r → M1 a = M a) := by
      refine ⟨Function.update (Function.update (Function.update M (n * n + 2 + r) (val r)) 1 1) 0 (n * n + 1 + r),
        ?_, ?_, ?_, ?_⟩
      · rw [show (10 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
        rw [run_succ, step_at' p o 38 _ _ _ _ (by omega) c38, ex_add _ _ _ _ (2 * (n * n + 2 + r)) _ _ (by rw [h0]; ring)]
        rw [run_succ, step_at' p o 39 _ _ _ _ (by omega) c39, ex_add _ _ _ _ (4 * (n * n + 2 + r)) _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false]; ring)]
        rw [run_succ, step_at' p o 40 _ _ _ _ (by omega) c40, ex_add _ _ _ _ (8 * (n * n + 2 + r)) _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false]; ring)]
        rw [run_succ, step_at' p o 41 _ _ _ _ (by omega) c41, ex_add _ _ _ _ (16 * (n * n + 2 + r)) _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false]; ring)]
        rw [run_succ, step_at' p o 42 _ _ _ _ (by omega) c42, ex_load _ _ _ (val r) _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, show 16 * (n * n + 2 + r) ≠ 1 by omega]; first | exact hS | exact hv)]
        rw [run_succ, step_at' p o 43 _ _ _ _ (by omega) c43, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h0]; omega)]
        rw [run_succ, step_at' p o 44 _ _ _ _ (by omega) c44, ex_store _ _ _ (n * n + 2 + r) (val r) _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false]; rw [hd]) (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false])]
        rw [run_succ, step_at' p o 45 _ _ _ _ (by omega) c45, ex_const]
        rw [run_succ, step_at' p o 46 _ _ _ _ (by omega) c46, ex_sub _ _ _ _ (n * n + 1 + r) _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, show (0 : ℕ) ≠ 1 by omega, show n * n + 2 + r ≠ 0 by omega, show ¬ ((0 : ℕ) = n * n + 2 + r) by omega]; rw [hd]; omega)]
        rw [run_succ, step_at' p o 47 _ _ _ _ (by omega) c47, ex_jump, run_zero]
        congr 1
        funext a
        simp only [Function.update_apply]
        split_ifs <;> first | rfl | omega
      · simp
      · simp only [Function.update_apply, ite_true, eq_self_iff_true]; rw [if_neg (by omega), if_neg (by omega)]
      · intro a a0 a1 ad; simp only [Function.update_apply, a0, a1, ad, if_false]
    obtain ⟨τ2, hτ2, r1, rO, rfr, rr⟩ := ih M1 R (by omega) f0
      (fun j hj => by rw [ffr _ (by omega) (by omega) (by nlinarith), hT j (by omega)])
      (by rw [ffr _ (by omega) (by omega) (by nlinarith), hS])
    refine ⟨10 + τ2, by omega, ?_⟩
    rw [run_add, e10]
    refine ⟨r1, fun j hj => ?_, fun a a0 a1 aj => ?_, rr⟩
    · rcases Nat.lt_or_ge j r with h | h
      · exact rO j h
      · have : j = r := by omega
        subst this
        rw [rfr _ (by omega) (by omega) (fun j' hj' => by omega), fd]
    · rw [rfr a a0 a1 (fun j' hj' => aj j' (by omega)), ffr a a0 a1 (aj r (by omega))]

set_option maxHeartbeats 16000000 in
lemma t_loop (n LVB BB cc TB : ℕ) (hLe : LVB % 2 = 0) (hB : BB % 2 = 1) (hTe : TB % 2 = 0) (hT : 0 < n → 40 ≤ TB)
    (hLT : TB + 16 * n ≤ LVB) :
    ∀ (r v : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), v + r = n →
      M 18 = LVB + 2 * n → M 10 = LVB + 2 * v → M 12 = BB + 2 * v → M 38 = TB + 16 * v →
      M 20 = cc → M 2 = 1 → M 4 = 2 → M 36 = 16 → M 0 = 0 →
      ∃ τ, τ ≤ 12 * r + 1 ∧ (planarRAMRun p ⟨o + 21, M, R⟩ τ).pc = o + 34 ∧
        (∀ j, v ≤ j → j < n → (planarRAMRun p ⟨o + 21, M, R⟩ τ).natMem (TB + 16 * j) = (if 1 ≤ M (BB + 2 * j) ∧ M (LVB + 2 * j) ≠ cc then 1 else 0)) ∧
        (planarRAMRun p ⟨o + 21, M, R⟩ τ).natMem 38 = TB + 16 * n ∧
        (∀ a, a ≠ 8 → a ≠ 10 → a ≠ 12 → a ≠ 38 → (∀ j, v ≤ j → j < n → a ≠ TB + 16 * j) → (planarRAMRun p ⟨o + 21, M, R⟩ τ).natMem a = M a) ∧
        (planarRAMRun p ⟨o + 21, M, R⟩ τ).realMem = R := by
  have c0 : p[o + 0]? = some (natConst 0 0) := by simpa using hcode 0 (by simp)
  have c1 : p[o + 1]? = some (natConst 2 1) := by simpa using hcode 1 (by simp)
  have c2 : p[o + 2]? = some (natConst 4 2) := by simpa using hcode 2 (by simp)
  have c3 : p[o + 3]? = some (natConst 36 16) := by simpa using hcode 3 (by simp)
  have c4 : p[o + 4]? = some (natAdd 24 32 32) := by simpa using hcode 4 (by simp)
  have c5 : p[o + 5]? = some (natAdd 18 28 24) := by simpa using hcode 5 (by simp)
  have c6 : p[o + 6]? = some (natConst 30 0) := by simpa using hcode 6 (by simp)
  have c7 : p[o + 7]? = some (natConst 6 0) := by simpa using hcode 7 (by simp)
  have c8 : p[o + 8]? = some (natBranch 32 6 (o + 12) (o + 9)) := by simpa using hcode 8 (by simp)
  have c9 : p[o + 9]? = some (natAdd 30 30 32) := by simpa using hcode 9 (by simp)
  have c10 : p[o + 10]? = some (natAdd 6 6 2) := by simpa using hcode 10 (by simp)
  have c11 : p[o + 11]? = some (jump (o + 8)) := by simpa using hcode 11 (by simp)
  have c12 : p[o + 12]? = some (natAdd 26 30 0) := by simpa using hcode 12 (by simp)
  have c13 : p[o + 13]? = some (natAdd 30 30 30) := by simpa using hcode 13 (by simp)
  have c14 : p[o + 14]? = some (natAdd 30 30 30) := by simpa using hcode 14 (by simp)
  have c15 : p[o + 15]? = some (natAdd 30 30 30) := by simpa using hcode 15 (by simp)
  have c16 : p[o + 16]? = some (natAdd 30 30 30) := by simpa using hcode 16 (by simp)
  have c17 : p[o + 17]? = some (natConst 8 32) := by simpa using hcode 17 (by simp)
  have c18 : p[o + 18]? = some (natAdd 38 30 8) := by simpa using hcode 18 (by simp)
  have c19 : p[o + 19]? = some (natAdd 10 28 0) := by simpa using hcode 19 (by simp)
  have c20 : p[o + 20]? = some (natAdd 12 22 0) := by simpa using hcode 20 (by simp)
  have c21 : p[o + 21]? = some (natBranch 18 10 (o + 34) (o + 22)) := by simpa using hcode 21 (by simp)
  have c22 : p[o + 22]? = some (natLoad 8 12) := by simpa using hcode 22 (by simp)
  have c23 : p[o + 23]? = some (natBranch 2 8 (o + 24) (o + 29)) := by simpa using hcode 23 (by simp)
  have c24 : p[o + 24]? = some (natLoad 8 10) := by simpa using hcode 24 (by simp)
  have c25 : p[o + 25]? = some (natBranch 8 20 (o + 26) (o + 27)) := by simpa using hcode 25 (by simp)
  have c26 : p[o + 26]? = some (natBranch 20 8 (o + 29) (o + 27)) := by simpa using hcode 26 (by simp)
  have c27 : p[o + 27]? = some (natStore 38 2) := by simpa using hcode 27 (by simp)
  have c28 : p[o + 28]? = some (jump (o + 30)) := by simpa using hcode 28 (by simp)
  have c29 : p[o + 29]? = some (natStore 38 0) := by simpa using hcode 29 (by simp)
  have c30 : p[o + 30]? = some (natAdd 10 10 4) := by simpa using hcode 30 (by simp)
  have c31 : p[o + 31]? = some (natAdd 12 12 4) := by simpa using hcode 31 (by simp)
  have c32 : p[o + 32]? = some (natAdd 38 38 36) := by simpa using hcode 32 (by simp)
  have c33 : p[o + 33]? = some (jump (o + 21)) := by simpa using hcode 33 (by simp)
  have c34 : p[o + 34]? = some (natAdd 0 26 32) := by simpa using hcode 34 (by simp)
  have c35 : p[o + 35]? = some (natAdd 0 0 2) := by simpa using hcode 35 (by simp)
  have c36 : p[o + 36]? = some (natAdd 8 30 36) := by simpa using hcode 36 (by simp)
  have c37 : p[o + 37]? = some (natStore 8 8) := by simpa using hcode 37 (by simp)
  have c38 : p[o + 38]? = some (natAdd 1 0 0) := by simpa using hcode 38 (by simp)
  have c39 : p[o + 39]? = some (natAdd 1 1 1) := by simpa using hcode 39 (by simp)
  have c40 : p[o + 40]? = some (natAdd 1 1 1) := by simpa using hcode 40 (by simp)
  have c41 : p[o + 41]? = some (natAdd 1 1 1) := by simpa using hcode 41 (by simp)
  have c42 : p[o + 42]? = some (natLoad 1 1) := by simpa using hcode 42 (by simp)
  have c43 : p[o + 43]? = some (natBranch 0 1 (o + 48) (o + 44)) := by simpa using hcode 43 (by simp)
  have c44 : p[o + 44]? = some (natStore 0 1) := by simpa using hcode 44 (by simp)
  have c45 : p[o + 45]? = some (natConst 1 1) := by simpa using hcode 45 (by simp)
  have c46 : p[o + 46]? = some (natSub 0 0 1) := by simpa using hcode 46 (by simp)
  have c47 : p[o + 47]? = some (jump (o + 38)) := by simpa using hcode 47 (by simp)
  intro r
  induction r with
  | zero =>
    intro v M R hv h18 h10 h12 h38 h20 h2 h4 h36 h0
    refine ⟨1, by omega, ?_⟩
    rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_at p o 21 _ rfl c21, run_zero]
    simp only [execInstr, show M 18 ≤ M 10 by omega, if_true]
    exact ⟨trivial, fun j h1 h2 => by omega, by rw [h38]; omega, fun a _ _ _ _ _ => trivial, trivial⟩
  | succ r ih =>
    intro v M R hv h18 h10 h12 h38 h20 h2 h4 h36 h0
    have hlt : ¬ M 18 ≤ M 10 := by omega
    have hvn : v < n := by omega
    have hT' := hT (by omega)
    have hne : LVB + 2 * v ≠ 8 ∧ BB + 2 * v ≠ 8 ∧ (TB + 16 * v ≠ 8) ∧ (TB + 16 * v ≠ 10) ∧ (TB + 16 * v ≠ 12) ∧
      (TB + 16 * v ≠ 38) ∧ ((8 : ℕ) ≠ TB + 16 * v) ∧ ((10 : ℕ) ≠ TB + 16 * v) ∧ ((12 : ℕ) ≠ TB + 16 * v) ∧
      ((38 : ℕ) ≠ TB + 16 * v) ∧ ((2 : ℕ) ≠ TB + 16 * v) ∧ ((4 : ℕ) ≠ TB + 16 * v) ∧ ((36 : ℕ) ≠ TB + 16 * v) ∧
      ((0 : ℕ) ≠ TB + 16 * v) ∧ ((20 : ℕ) ≠ TB + 16 * v) := by omega
    obtain ⟨bt, hb⟩ : ∃ bt, M (BB + 2 * v) = bt := ⟨_, rfl⟩
    obtain ⟨md, hm⟩ : ∃ md, M (LVB + 2 * v) = md := ⟨_, rfl⟩
    have one : ∃ τ1, τ1 ≤ 12 ∧ (planarRAMRun p ⟨o + 21, M, R⟩ τ1).pc = o + 21 ∧
        (planarRAMRun p ⟨o + 21, M, R⟩ τ1).natMem (TB + 16 * v) = (if 1 ≤ bt ∧ md ≠ cc then 1 else 0) ∧
        (planarRAMRun p ⟨o + 21, M, R⟩ τ1).natMem 10 = LVB + 2 * (v + 1) ∧ (planarRAMRun p ⟨o + 21, M, R⟩ τ1).natMem 12 = BB + 2 * (v + 1) ∧
        (planarRAMRun p ⟨o + 21, M, R⟩ τ1).natMem 38 = TB + 16 * (v + 1) ∧
        (∀ a, a ≠ 8 → a ≠ 10 → a ≠ 12 → a ≠ 38 → a ≠ TB + 16 * v → (planarRAMRun p ⟨o + 21, M, R⟩ τ1).natMem a = M a) ∧
        (planarRAMRun p ⟨o + 21, M, R⟩ τ1).realMem = R := by
      by_cases a0 : 1 ≤ bt
      · by_cases a1 : md ≤ cc
        · by_cases a2 : cc ≤ md
          · have hc : ¬ (1 ≤ bt ∧ md ≠ cc) := by omega
            refine ⟨11, by omega, ?_⟩
            rw [show (11 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
            rw [run_succ, step_at' p o 21 _ _ _ _ (by omega) c21, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2] <;> first | trivial | omega)]
            rw [run_succ, step_at' p o 22 _ _ _ _ (by omega) c22, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p o 23 _ _ _ _ (by omega) c23, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2] <;> first | trivial | omega)]
            rw [run_succ, step_at' p o 24 _ _ _ _ (by omega) c24, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p o 25 _ _ _ _ (by omega) c25, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2] <;> first | trivial | omega)]
            rw [run_succ, step_at' p o 26 _ _ _ _ (by omega) c26, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2] <;> first | trivial | omega)]
            rw [run_succ, step_at' p o 29 _ _ _ _ (by omega) c29, ex_store _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2] <;> first | rfl | omega) | rfl) (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p o 30 _ _ _ _ (by omega) c30, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p o 31 _ _ _ _ (by omega) c31, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p o 32 _ _ _ _ (by omega) c32, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p o 33 _ _ _ _ (by omega) c33, ex_jump]
            rw [run_zero]
            try rfl
            refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
            all_goals first
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, if_neg hc]; done)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, hne, if_neg hc]; done)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2, if_neg hc]; done)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2, if_neg hc] <;> omega)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2, if_neg hc]; ring1)
              | (intro a a8 a10 a12 a38 aT; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, a8, a10, a12, a38, aT])
          · have hc : 1 ≤ bt ∧ md ≠ cc := ⟨a0, by omega⟩
            refine ⟨12, by omega, ?_⟩
            rw [show (12 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
            rw [run_succ, step_at' p o 21 _ _ _ _ (by omega) c21, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2] <;> first | trivial | omega)]
            rw [run_succ, step_at' p o 22 _ _ _ _ (by omega) c22, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p o 23 _ _ _ _ (by omega) c23, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2] <;> first | trivial | omega)]
            rw [run_succ, step_at' p o 24 _ _ _ _ (by omega) c24, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p o 25 _ _ _ _ (by omega) c25, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2] <;> first | trivial | omega)]
            rw [run_succ, step_at' p o 26 _ _ _ _ (by omega) c26, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2] <;> first | trivial | omega)]
            rw [run_succ, step_at' p o 27 _ _ _ _ (by omega) c27, ex_store _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2] <;> first | rfl | omega) | rfl) (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p o 28 _ _ _ _ (by omega) c28, ex_jump]
            rw [run_succ, step_at' p o 30 _ _ _ _ (by omega) c30, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p o 31 _ _ _ _ (by omega) c31, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p o 32 _ _ _ _ (by omega) c32, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p o 33 _ _ _ _ (by omega) c33, ex_jump]
            rw [run_zero]
            try rfl
            refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
            all_goals first
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, if_pos hc]; done)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, hne, if_pos hc]; done)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2, if_pos hc]; done)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2, if_pos hc] <;> omega)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, a2, if_pos hc]; ring1)
              | (intro a a8 a10 a12 a38 aT; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, a8, a10, a12, a38, aT])
        · have hc : 1 ≤ bt ∧ md ≠ cc := ⟨a0, by omega⟩
          refine ⟨11, by omega, ?_⟩
          rw [show (11 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
          rw [run_succ, step_at' p o 21 _ _ _ _ (by omega) c21, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1] <;> first | trivial | omega)]
          rw [run_succ, step_at' p o 22 _ _ _ _ (by omega) c22, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p o 23 _ _ _ _ (by omega) c23, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1] <;> first | trivial | omega)]
          rw [run_succ, step_at' p o 24 _ _ _ _ (by omega) c24, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p o 25 _ _ _ _ (by omega) c25, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1] <;> first | trivial | omega)]
          rw [run_succ, step_at' p o 27 _ _ _ _ (by omega) c27, ex_store _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1] <;> first | rfl | omega) | rfl) (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p o 28 _ _ _ _ (by omega) c28, ex_jump]
          rw [run_succ, step_at' p o 30 _ _ _ _ (by omega) c30, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p o 31 _ _ _ _ (by omega) c31, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p o 32 _ _ _ _ (by omega) c32, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p o 33 _ _ _ _ (by omega) c33, ex_jump]
          rw [run_zero]
          try rfl
          refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
          all_goals first
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, if_pos hc]; done)
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, hne, if_pos hc]; done)
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, if_pos hc]; done)
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, if_pos hc] <;> omega)
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, a1, if_pos hc]; ring1)
            | (intro a a8 a10 a12 a38 aT; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, a8, a10, a12, a38, aT])
      · have hc : ¬ (1 ≤ bt ∧ md ≠ cc) := by omega
        refine ⟨8, by omega, ?_⟩
        rw [show (8 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
        rw [run_succ, step_at' p o 21 _ _ _ _ (by omega) c21, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0] <;> first | trivial | omega)]
        rw [run_succ, step_at' p o 22 _ _ _ _ (by omega) c22, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0] <;> first | rfl | omega) | rfl)]
        rw [run_succ, step_at' p o 23 _ _ _ _ (by omega) c23, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0] <;> first | trivial | omega)]
        rw [run_succ, step_at' p o 29 _ _ _ _ (by omega) c29, ex_store _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0] <;> first | rfl | omega) | rfl) (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0] <;> first | rfl | omega) | rfl)]
        rw [run_succ, step_at' p o 30 _ _ _ _ (by omega) c30, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0] <;> first | rfl | omega) | rfl)]
        rw [run_succ, step_at' p o 31 _ _ _ _ (by omega) c31, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0] <;> first | rfl | omega) | rfl)]
        rw [run_succ, step_at' p o 32 _ _ _ _ (by omega) c32, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0] <;> first | rfl | omega) | rfl)]
        rw [run_succ, step_at' p o 33 _ _ _ _ (by omega) c33, ex_jump]
        rw [run_zero]
        try rfl
        refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
        all_goals first
          | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, if_neg hc]; done)
          | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, hne, if_neg hc]; done)
          | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, if_neg hc]; done)
          | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, if_neg hc] <;> omega)
          | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h18, h10, h12, h38, h20, h2, h4, h36, h0, hlt, hb, hm, hne, a0, if_neg hc]; ring1)
          | (intro a a8 a10 a12 a38 aT; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, a8, a10, a12, a38, aT])
    obtain ⟨τ1, hτ1, q1, qT, q10, q12, q38, qfr, qr⟩ := one
    set S1 := planarRAMRun p ⟨o + 21, M, R⟩ τ1 with hS1
    obtain ⟨pc1, M1, R1⟩ := S1
    simp only at q1 qT q10 q12 q38 qfr qr
    subst q1; subst R1
    have f : ∀ a, a ≠ 8 → a ≠ 10 → a ≠ 12 → a ≠ 38 → a ≠ TB + 16 * v → M1 a = M a := qfr
    obtain ⟨τ2, hτ2, r1, rT, r38, rfr, rr⟩ := ih (v + 1) M1 R (by omega)
      (by rw [f 18 (by omega) (by omega) (by omega) (by omega) (by omega), h18]) q10 q12 q38
      (by rw [f 20 (by omega) (by omega) (by omega) (by omega) (by omega), h20])
      (by rw [f 2 (by omega) (by omega) (by omega) (by omega) (by omega), h2])
      (by rw [f 4 (by omega) (by omega) (by omega) (by omega) (by omega), h4])
      (by rw [f 36 (by omega) (by omega) (by omega) (by omega) (by omega), h36])
      (by rw [f 0 (by omega) (by omega) (by omega) (by omega) (by omega), h0])
    refine ⟨τ1 + τ2, by omega, ?_⟩
    rw [run_add, ← hS1]
    refine ⟨r1, fun j hj1 hj2 => ?_, r38, fun a a8 a10 a12 a38 aT => ?_, rr⟩
    · rcases Nat.eq_or_lt_of_le hj1 with h | h
      · subst h
        rw [rfr _ (by omega) (by omega) (by omega) (by omega) (fun j' h1 _ => by omega), qT, hb, hm]
      · rw [rT j h hj2, f (BB + 2 * j) (by omega) (by omega) (by omega) (by omega) (by omega),
          f (LVB + 2 * j) (by omega) (by omega) (by omega) (by omega) (by omega)]
    · rw [rfr a a8 a10 a12 a38 (fun j h1 h2 => aT j (by omega) h2), f a a8 a10 a12 a38 (aT v le_rfl (by omega))]

set_option maxHeartbeats 4000000 in
lemma sq_loop (K V : ℕ) :
    ∀ (r i acc : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), i + r = K →
      M 32 = K → M 32 = V → M 2 = 1 → M 6 = i → M 30 = acc →
      ∃ τ, τ ≤ 4 * r + 1 ∧ (planarRAMRun p ⟨o + 8, M, R⟩ τ).pc = o + 12 ∧
        (planarRAMRun p ⟨o + 8, M, R⟩ τ).natMem 30 = acc + r * V ∧
        (∀ a, a ≠ 6 → a ≠ 30 → (planarRAMRun p ⟨o + 8, M, R⟩ τ).natMem a = M a) ∧
        (planarRAMRun p ⟨o + 8, M, R⟩ τ).realMem = R := by
  have c0 : p[o + 0]? = some (natConst 0 0) := by simpa using hcode 0 (by simp)
  have c1 : p[o + 1]? = some (natConst 2 1) := by simpa using hcode 1 (by simp)
  have c2 : p[o + 2]? = some (natConst 4 2) := by simpa using hcode 2 (by simp)
  have c3 : p[o + 3]? = some (natConst 36 16) := by simpa using hcode 3 (by simp)
  have c4 : p[o + 4]? = some (natAdd 24 32 32) := by simpa using hcode 4 (by simp)
  have c5 : p[o + 5]? = some (natAdd 18 28 24) := by simpa using hcode 5 (by simp)
  have c6 : p[o + 6]? = some (natConst 30 0) := by simpa using hcode 6 (by simp)
  have c7 : p[o + 7]? = some (natConst 6 0) := by simpa using hcode 7 (by simp)
  have c8 : p[o + 8]? = some (natBranch 32 6 (o + 12) (o + 9)) := by simpa using hcode 8 (by simp)
  have c9 : p[o + 9]? = some (natAdd 30 30 32) := by simpa using hcode 9 (by simp)
  have c10 : p[o + 10]? = some (natAdd 6 6 2) := by simpa using hcode 10 (by simp)
  have c11 : p[o + 11]? = some (jump (o + 8)) := by simpa using hcode 11 (by simp)
  have c12 : p[o + 12]? = some (natAdd 26 30 0) := by simpa using hcode 12 (by simp)
  have c13 : p[o + 13]? = some (natAdd 30 30 30) := by simpa using hcode 13 (by simp)
  have c14 : p[o + 14]? = some (natAdd 30 30 30) := by simpa using hcode 14 (by simp)
  have c15 : p[o + 15]? = some (natAdd 30 30 30) := by simpa using hcode 15 (by simp)
  have c16 : p[o + 16]? = some (natAdd 30 30 30) := by simpa using hcode 16 (by simp)
  have c17 : p[o + 17]? = some (natConst 8 32) := by simpa using hcode 17 (by simp)
  have c18 : p[o + 18]? = some (natAdd 38 30 8) := by simpa using hcode 18 (by simp)
  have c19 : p[o + 19]? = some (natAdd 10 28 0) := by simpa using hcode 19 (by simp)
  have c20 : p[o + 20]? = some (natAdd 12 22 0) := by simpa using hcode 20 (by simp)
  have c21 : p[o + 21]? = some (natBranch 18 10 (o + 34) (o + 22)) := by simpa using hcode 21 (by simp)
  have c22 : p[o + 22]? = some (natLoad 8 12) := by simpa using hcode 22 (by simp)
  have c23 : p[o + 23]? = some (natBranch 2 8 (o + 24) (o + 29)) := by simpa using hcode 23 (by simp)
  have c24 : p[o + 24]? = some (natLoad 8 10) := by simpa using hcode 24 (by simp)
  have c25 : p[o + 25]? = some (natBranch 8 20 (o + 26) (o + 27)) := by simpa using hcode 25 (by simp)
  have c26 : p[o + 26]? = some (natBranch 20 8 (o + 29) (o + 27)) := by simpa using hcode 26 (by simp)
  have c27 : p[o + 27]? = some (natStore 38 2) := by simpa using hcode 27 (by simp)
  have c28 : p[o + 28]? = some (jump (o + 30)) := by simpa using hcode 28 (by simp)
  have c29 : p[o + 29]? = some (natStore 38 0) := by simpa using hcode 29 (by simp)
  have c30 : p[o + 30]? = some (natAdd 10 10 4) := by simpa using hcode 30 (by simp)
  have c31 : p[o + 31]? = some (natAdd 12 12 4) := by simpa using hcode 31 (by simp)
  have c32 : p[o + 32]? = some (natAdd 38 38 36) := by simpa using hcode 32 (by simp)
  have c33 : p[o + 33]? = some (jump (o + 21)) := by simpa using hcode 33 (by simp)
  have c34 : p[o + 34]? = some (natAdd 0 26 32) := by simpa using hcode 34 (by simp)
  have c35 : p[o + 35]? = some (natAdd 0 0 2) := by simpa using hcode 35 (by simp)
  have c36 : p[o + 36]? = some (natAdd 8 30 36) := by simpa using hcode 36 (by simp)
  have c37 : p[o + 37]? = some (natStore 8 8) := by simpa using hcode 37 (by simp)
  have c38 : p[o + 38]? = some (natAdd 1 0 0) := by simpa using hcode 38 (by simp)
  have c39 : p[o + 39]? = some (natAdd 1 1 1) := by simpa using hcode 39 (by simp)
  have c40 : p[o + 40]? = some (natAdd 1 1 1) := by simpa using hcode 40 (by simp)
  have c41 : p[o + 41]? = some (natAdd 1 1 1) := by simpa using hcode 41 (by simp)
  have c42 : p[o + 42]? = some (natLoad 1 1) := by simpa using hcode 42 (by simp)
  have c43 : p[o + 43]? = some (natBranch 0 1 (o + 48) (o + 44)) := by simpa using hcode 43 (by simp)
  have c44 : p[o + 44]? = some (natStore 0 1) := by simpa using hcode 44 (by simp)
  have c45 : p[o + 45]? = some (natConst 1 1) := by simpa using hcode 45 (by simp)
  have c46 : p[o + 46]? = some (natSub 0 0 1) := by simpa using hcode 46 (by simp)
  have c47 : p[o + 47]? = some (jump (o + 38)) := by simpa using hcode 47 (by simp)
  intro r
  induction r with
  | zero =>
    intro i acc M R hi hL hX h2 h6 hA
    refine ⟨1, by omega, ?_⟩
    rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_at p o 8 _ rfl c8, run_zero]
    simp only [execInstr, show M 32 ≤ M 6 by omega, if_true]
    exact ⟨trivial, by simp [hA], fun a _ _ => trivial, trivial⟩
  | succ r ih =>
    intro i acc M R hi hL hX h2 h6 hA
    have hlt : ¬ M 32 ≤ M 6 := by omega
    obtain ⟨τ2, hτ2, r1, rA, rfr, rr⟩ := ih (i + 1) (acc + V)
      (Function.update (Function.update M 30 (acc + V)) 6 (i + 1)) R (by omega)
      (by simp [Function.update_apply, hL]) (by simp [Function.update_apply, hX])
      (by simp [Function.update_apply, h2]) (by simp) (by simp [Function.update_apply])
    refine ⟨4 + τ2, by omega, ?_⟩
    have e4 : planarRAMRun p ⟨o + 8, M, R⟩ 4 =
        ⟨o + 8, Function.update (Function.update M 30 (acc + V)) 6 (i + 1), R⟩ := by
      rw [show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 from rfl, run_succ, step_at' p o 8 _ _ _ _ (by omega) c8,
        ex_brf _ _ _ _ _ _ _ hlt, run_succ, step_at' p o 9 _ _ _ _ (by omega) c9,
        ex_add _ _ _ _ _ _ _ (by rw [hA, hX]), run_succ, step_at' p o 10 _ _ _ _ (by omega) c10,
        ex_add _ _ _ _ _ _ _ (by simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte, h6, h2]; rfl),
        run_succ, step_at' p o 11 _ _ _ _ (by omega) c11, ex_jump, run_zero]
    rw [run_add, e4]
    refine ⟨r1, by rw [rA]; ring, fun a a6 aA => ?_, rr⟩
    rw [rfr a a6 aA, Function.update_of_ne a6, Function.update_of_ne aA]

set_option maxHeartbeats 16000000 in
lemma out_write (n LVB BB cc : ℕ) (hLe : LVB % 2 = 0) (hB : BB % 2 = 1) (hL : 32 + 16 * n * n + 16 * n ≤ LVB)
    (M : ℕ → ℕ) (R : ℕ → ℝ) (h32 : M 32 = n) (h28 : M 28 = LVB) (h20 : M 20 = cc) (h22 : M 22 = BB) :
    ∃ τ, τ ≤ 26 * n + 29 ∧ (planarRAMRun p ⟨o, M, R⟩ τ).pc = o + 48 ∧
      (∀ j, j < n → (planarRAMRun p ⟨o, M, R⟩ τ).natMem (2 + n * n + j) = (if 1 ≤ M (BB + 2 * j) ∧ M (LVB + 2 * j) ≠ cc then 1 else 0)) := by
  have c0 : p[o + 0]? = some (natConst 0 0) := by simpa using hcode 0 (by simp)
  have c1 : p[o + 1]? = some (natConst 2 1) := by simpa using hcode 1 (by simp)
  have c2 : p[o + 2]? = some (natConst 4 2) := by simpa using hcode 2 (by simp)
  have c3 : p[o + 3]? = some (natConst 36 16) := by simpa using hcode 3 (by simp)
  have c4 : p[o + 4]? = some (natAdd 24 32 32) := by simpa using hcode 4 (by simp)
  have c5 : p[o + 5]? = some (natAdd 18 28 24) := by simpa using hcode 5 (by simp)
  have c6 : p[o + 6]? = some (natConst 30 0) := by simpa using hcode 6 (by simp)
  have c7 : p[o + 7]? = some (natConst 6 0) := by simpa using hcode 7 (by simp)
  have c8 : p[o + 8]? = some (natBranch 32 6 (o + 12) (o + 9)) := by simpa using hcode 8 (by simp)
  have c9 : p[o + 9]? = some (natAdd 30 30 32) := by simpa using hcode 9 (by simp)
  have c10 : p[o + 10]? = some (natAdd 6 6 2) := by simpa using hcode 10 (by simp)
  have c11 : p[o + 11]? = some (jump (o + 8)) := by simpa using hcode 11 (by simp)
  have c12 : p[o + 12]? = some (natAdd 26 30 0) := by simpa using hcode 12 (by simp)
  have c13 : p[o + 13]? = some (natAdd 30 30 30) := by simpa using hcode 13 (by simp)
  have c14 : p[o + 14]? = some (natAdd 30 30 30) := by simpa using hcode 14 (by simp)
  have c15 : p[o + 15]? = some (natAdd 30 30 30) := by simpa using hcode 15 (by simp)
  have c16 : p[o + 16]? = some (natAdd 30 30 30) := by simpa using hcode 16 (by simp)
  have c17 : p[o + 17]? = some (natConst 8 32) := by simpa using hcode 17 (by simp)
  have c18 : p[o + 18]? = some (natAdd 38 30 8) := by simpa using hcode 18 (by simp)
  have c19 : p[o + 19]? = some (natAdd 10 28 0) := by simpa using hcode 19 (by simp)
  have c20 : p[o + 20]? = some (natAdd 12 22 0) := by simpa using hcode 20 (by simp)
  have c21 : p[o + 21]? = some (natBranch 18 10 (o + 34) (o + 22)) := by simpa using hcode 21 (by simp)
  have c22 : p[o + 22]? = some (natLoad 8 12) := by simpa using hcode 22 (by simp)
  have c23 : p[o + 23]? = some (natBranch 2 8 (o + 24) (o + 29)) := by simpa using hcode 23 (by simp)
  have c24 : p[o + 24]? = some (natLoad 8 10) := by simpa using hcode 24 (by simp)
  have c25 : p[o + 25]? = some (natBranch 8 20 (o + 26) (o + 27)) := by simpa using hcode 25 (by simp)
  have c26 : p[o + 26]? = some (natBranch 20 8 (o + 29) (o + 27)) := by simpa using hcode 26 (by simp)
  have c27 : p[o + 27]? = some (natStore 38 2) := by simpa using hcode 27 (by simp)
  have c28 : p[o + 28]? = some (jump (o + 30)) := by simpa using hcode 28 (by simp)
  have c29 : p[o + 29]? = some (natStore 38 0) := by simpa using hcode 29 (by simp)
  have c30 : p[o + 30]? = some (natAdd 10 10 4) := by simpa using hcode 30 (by simp)
  have c31 : p[o + 31]? = some (natAdd 12 12 4) := by simpa using hcode 31 (by simp)
  have c32 : p[o + 32]? = some (natAdd 38 38 36) := by simpa using hcode 32 (by simp)
  have c33 : p[o + 33]? = some (jump (o + 21)) := by simpa using hcode 33 (by simp)
  have c34 : p[o + 34]? = some (natAdd 0 26 32) := by simpa using hcode 34 (by simp)
  have c35 : p[o + 35]? = some (natAdd 0 0 2) := by simpa using hcode 35 (by simp)
  have c36 : p[o + 36]? = some (natAdd 8 30 36) := by simpa using hcode 36 (by simp)
  have c37 : p[o + 37]? = some (natStore 8 8) := by simpa using hcode 37 (by simp)
  have c38 : p[o + 38]? = some (natAdd 1 0 0) := by simpa using hcode 38 (by simp)
  have c39 : p[o + 39]? = some (natAdd 1 1 1) := by simpa using hcode 39 (by simp)
  have c40 : p[o + 40]? = some (natAdd 1 1 1) := by simpa using hcode 40 (by simp)
  have c41 : p[o + 41]? = some (natAdd 1 1 1) := by simpa using hcode 41 (by simp)
  have c42 : p[o + 42]? = some (natLoad 1 1) := by simpa using hcode 42 (by simp)
  have c43 : p[o + 43]? = some (natBranch 0 1 (o + 48) (o + 44)) := by simpa using hcode 43 (by simp)
  have c44 : p[o + 44]? = some (natStore 0 1) := by simpa using hcode 44 (by simp)
  have c45 : p[o + 45]? = some (natConst 1 1) := by simpa using hcode 45 (by simp)
  have c46 : p[o + 46]? = some (natSub 0 0 1) := by simpa using hcode 46 (by simp)
  have c47 : p[o + 47]? = some (jump (o + 38)) := by simpa using hcode 47 (by simp)
  have sA : (planarRAMRun p ⟨o, M, R⟩ 8).pc = o + 8 ∧ (planarRAMRun p ⟨o, M, R⟩ 8).natMem 0 = 0 ∧ (planarRAMRun p ⟨o, M, R⟩ 8).natMem 2 = 1 ∧ (planarRAMRun p ⟨o, M, R⟩ 8).natMem 4 = 2 ∧
      (planarRAMRun p ⟨o, M, R⟩ 8).natMem 36 = 16 ∧ (planarRAMRun p ⟨o, M, R⟩ 8).natMem 24 = 2 * n ∧ (planarRAMRun p ⟨o, M, R⟩ 8).natMem 18 = LVB + 2 * n ∧ (planarRAMRun p ⟨o, M, R⟩ 8).natMem 30 = 0 ∧
      (planarRAMRun p ⟨o, M, R⟩ 8).natMem 6 = 0 ∧ (∀ a, a ≠ 0 → a ≠ 2 → a ≠ 4 → a ≠ 36 → a ≠ 24 → a ≠ 18 → a ≠ 30 → a ≠ 6 → (planarRAMRun p ⟨o, M, R⟩ 8).natMem a = M a) ∧ (planarRAMRun p ⟨o, M, R⟩ 8).realMem = R := by
    rw [show (8 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
    rw [run_succ, step_at' p o 0 _ _ _ _ (by omega) c0, ex_const]
    rw [run_succ, step_at' p o 1 _ _ _ _ (by omega) c1, ex_const]
    rw [run_succ, step_at' p o 2 _ _ _ _ (by omega) c2, ex_const]
    rw [run_succ, step_at' p o 3 _ _ _ _ (by omega) c3, ex_const]
    rw [run_succ, step_at' p o 4 _ _ _ _ (by omega) c4, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h32, h28] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p o 5 _ _ _ _ (by omega) c5, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h32, h28] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p o 6 _ _ _ _ (by omega) c6, ex_const]
    rw [run_succ, step_at' p o 7 _ _ _ _ (by omega) c7, ex_const]
    rw [run_zero]
    try rfl
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    all_goals first
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h32, h28]; done)
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h32, h28] <;> omega)
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, h32, h28]; ring1)
      | (intro a a0 a2 a4 a36 a24 a18 a30 a6; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, a0, a2, a4, a36, a24, a18, a30, a6])
  obtain ⟨a1, a0, a2, a4, a36, a24, a18, a30, a6, afr, ar⟩ := sA
  set S8 := planarRAMRun p ⟨o, M, R⟩ 8 with hS8
  obtain ⟨pc8, M8, R8⟩ := S8
  simp only at a1 a0 a2 a4 a36 a24 a18 a30 a6 afr ar
  subst a1; subst R8
  have f8 : ∀ a, 38 ≤ a → M8 a = M a := fun a ha => afr a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have g32 : M8 32 = n := by rw [afr 32 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h32]
  obtain ⟨τ1, hτ1, l1, l30, lfr, lr⟩ := sq_loop p o hcode n n n 0 0 M8 R (by omega) g32 g32 a2 a6 a30
  set S9 := planarRAMRun p ⟨o + 8, M8, R⟩ τ1 with hS9
  obtain ⟨pc9, M1, R9⟩ := S9
  simp only at l1 l30 lfr lr
  subst l1; subst R9
  have g30 : M1 30 = n * n := by rw [l30]; ring
  have e1 : ∀ a, a ≠ 6 → a ≠ 30 → M1 a = M8 a := lfr
  have m0 : M1 0 = 0 := by rw [e1 0 (by omega) (by omega), a0]
  have m28 : M1 28 = LVB := by rw [e1 28 (by omega) (by omega), afr 28 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h28]
  have m22 : M1 22 = BB := by rw [e1 22 (by omega) (by omega), afr 22 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h22]
  have sB : (planarRAMRun p ⟨o + 12, M1, R⟩ 9).pc = o + 21 ∧ (planarRAMRun p ⟨o + 12, M1, R⟩ 9).natMem 26 = n * n ∧ (planarRAMRun p ⟨o + 12, M1, R⟩ 9).natMem 30 = 16 * (n * n) ∧
      (planarRAMRun p ⟨o + 12, M1, R⟩ 9).natMem 38 = 32 + 16 * (n * n) + 16 * 0 ∧ (planarRAMRun p ⟨o + 12, M1, R⟩ 9).natMem 10 = LVB + 2 * 0 ∧ (planarRAMRun p ⟨o + 12, M1, R⟩ 9).natMem 12 = BB + 2 * 0 ∧
      (∀ a, a ≠ 26 → a ≠ 30 → a ≠ 8 → a ≠ 38 → a ≠ 10 → a ≠ 12 → (planarRAMRun p ⟨o + 12, M1, R⟩ 9).natMem a = M1 a) ∧ (planarRAMRun p ⟨o + 12, M1, R⟩ 9).realMem = R := by
    rw [show (9 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
    rw [run_succ, step_at' p o 12 _ _ _ _ (by omega) c12, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g30, m0, m28, m22] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p o 13 _ _ _ _ (by omega) c13, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g30, m0, m28, m22] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p o 14 _ _ _ _ (by omega) c14, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g30, m0, m28, m22] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p o 15 _ _ _ _ (by omega) c15, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g30, m0, m28, m22] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p o 16 _ _ _ _ (by omega) c16, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g30, m0, m28, m22] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p o 17 _ _ _ _ (by omega) c17, ex_const]
    rw [run_succ, step_at' p o 18 _ _ _ _ (by omega) c18, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g30, m0, m28, m22] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p o 19 _ _ _ _ (by omega) c19, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g30, m0, m28, m22] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p o 20 _ _ _ _ (by omega) c20, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g30, m0, m28, m22] <;> first | rfl | omega) | rfl)]
    rw [run_zero]
    try rfl
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    all_goals first
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, g30, m0, m28, m22]; done)
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, g30, m0, m28, m22] <;> omega)
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, g30, m0, m28, m22]; ring1)
      | (intro a a26 a30 a8 a38 a10 a12; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, a26, a30, a8, a38, a10, a12])
  obtain ⟨b1, b26, b30, b38, b10, b12, bfr, br⟩ := sB
  set S10 := planarRAMRun p ⟨o + 12, M1, R⟩ 9 with hS10
  obtain ⟨pc10, M2, R10⟩ := S10
  simp only at b1 b26 b30 b38 b10 b12 bfr br
  subst b1; subst R10
  have e2 : ∀ a, (a % 2 = 1 ∨ 40 ≤ a) → M2 a = M a := fun a ha => by
    rw [bfr a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), e1 a (by omega) (by omega),
      afr a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  have k2 : ∀ a, a ≠ 26 → a ≠ 30 → a ≠ 8 → a ≠ 38 → a ≠ 10 → a ≠ 12 → a ≠ 6 → M2 a = M8 a := fun a a26 a30 a8 a38 a10 a12 a6 => by
    rw [bfr a a26 a30 a8 a38 a10 a12, e1 a a6 a30]
  have hTe : (32 + 16 * (n * n)) % 2 = 0 := by omega
  obtain ⟨τt, hτt, t1, tT, t38, tfr, tr⟩ := t_loop p o hcode n LVB BB cc (32 + 16 * (n * n)) hLe hB hTe
    (fun hn => by have := Nat.mul_le_mul hn hn; omega) (by nlinarith) n 0 M2 R (by omega)
    (by rw [k2 18 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), a18]) b10 b12 b38
    (by rw [k2 20 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      afr 20 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h20])
    (by rw [k2 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), a2])
    (by rw [k2 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), a4])
    (by rw [k2 36 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), a36])
    (by rw [k2 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), a0])
  set S11 := planarRAMRun p ⟨o + 21, M2, R⟩ τt with hS11
  obtain ⟨pc11, M3, R11⟩ := S11
  simp only at t1 tT t38 tfr tr
  subst t1; subst R11
  have m26 : M3 26 = n * n := by
    rw [tfr 26 (by omega) (by omega) (by omega) (by omega) (fun j _ _ => by omega), b26]
  have m32 : M3 32 = n := by
    rw [tfr 32 (by omega) (by omega) (by omega) (by omega) (fun j _ hj => by have := Nat.mul_le_mul (show 1 ≤ n by omega) (show 1 ≤ n by omega); omega),
      k2 32 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g32]
  have m30 : M3 30 = 16 * (n * n) := by
    rw [tfr 30 (by omega) (by omega) (by omega) (by omega) (fun j _ _ => by omega), b30]
  have m36 : M3 36 = 16 := by
    rw [tfr 36 (by omega) (by omega) (by omega) (by omega) (fun j _ _ => by omega),
      k2 36 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), a36]
  have m2 : M3 2 = 1 := by
    rw [tfr 2 (by omega) (by omega) (by omega) (by omega) (fun j _ _ => by omega),
      k2 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), a2]
  obtain ⟨M4, e4, f0, fS, ffr⟩ : ∃ M4, planarRAMRun p ⟨o + 34, M3, R⟩ 4 = ⟨o + 38, M4, R⟩ ∧
      M4 0 = n * n + 1 + n ∧ M4 (16 * (n * n + 1)) = 16 * (n * n + 1) ∧
      (∀ a, a ≠ 0 → a ≠ 8 → a ≠ 16 * (n * n + 1) → M4 a = M3 a) := by
    refine ⟨Function.update (Function.update (Function.update (Function.update M3 0 (n * n + n)) 0 (n * n + n + 1))
      8 (16 * (n * n) + 16)) (16 * (n * n) + 16) (16 * (n * n) + 16), ?_, ?_, ?_, ?_⟩
    · rw [show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 from rfl]
      rw [run_succ, step_at' p o 34 _ _ _ _ (by omega) c34, ex_add _ _ _ _ (n * n + n) _ _ (by rw [m26, m32])]
      rw [run_succ, step_at' p o 35 _ _ _ _ (by omega) c35, ex_add _ _ _ _ (n * n + n + 1) _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, m2])]
      rw [run_succ, step_at' p o 36 _ _ _ _ (by omega) c36, ex_add _ _ _ _ (16 * (n * n) + 16) _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false, m30, m36])]
      rw [run_succ, step_at' p o 37 _ _ _ _ (by omega) c37, ex_store _ _ _ (16 * (n * n) + 16) (16 * (n * n) + 16) _ _
        (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false]) (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, zero_add, ne_eq, not_true_eq_false, false_and, if_false]), run_zero]
    · simp only [Function.update_apply]
      rw [if_neg (by omega), if_neg (by omega)]; simp only [ite_true]; ring
    · simp only [Function.update_apply]; rw [if_pos (by ring)]; ring
    · intro a a0 a8 aS
      simp only [Function.update_apply]
      rw [if_neg (by intro h; apply aS; rw [h]; ring), if_neg a8, if_neg a0, if_neg a0]
  have hval : ∀ j, (if 1 ≤ M (BB + 2 * j) ∧ M (LVB + 2 * j) ≠ cc then 1 else 0) ≤ 1 := fun j => by split_ifs <;> omega
  obtain ⟨τc, hτc, c1, cO, cfr, cr⟩ := copy_loop p o hcode n (fun j => if 1 ≤ M (BB + 2 * j) ∧ M (LVB + 2 * j) ≠ cc then 1 else 0)
    hval n M4 R le_rfl f0
    (fun j hj => by
      have hn1 : 1 ≤ n := by omega
      have := Nat.mul_le_mul hn1 hn1
      rw [ffr _ (by omega) (by omega) (by omega), show 16 * (n * n + 2 + j) = 32 + 16 * (n * n) + 16 * j by ring,
        tT j (Nat.zero_le _) hj, e2 _ (Or.inl (by omega)), e2 _ (Or.inr (by omega))])
    fS
  refine ⟨8 + τ1 + 9 + τt + 4 + τc, by omega, ?_⟩
  rw [run_add, run_add, run_add, run_add, run_add, ← hS8, ← hS9, ← hS10, ← hS11, e4]
  refine ⟨c1, fun j hj => ?_⟩
  rw [show 2 + n * n + j = n * n + 2 + j by ring, cO j hj]

end

end OU

open WilliamsonShmoys PlanarRAMInstruction
open Classical in
theorem solution (p : List PlanarRAMInstruction) (o : ℕ)
    (hcode : CodeAt p o
    [natConst 0 0,
      natConst 2 1,
      natConst 4 2,
      natConst 36 16,
      natAdd 24 32 32,
      natAdd 18 28 24,
      natConst 30 0,
      natConst 6 0,
      natBranch 32 6 (o + 12) (o + 9),
      natAdd 30 30 32,
      natAdd 6 6 2,
      jump (o + 8),
      natAdd 26 30 0,
      natAdd 30 30 30,
      natAdd 30 30 30,
      natAdd 30 30 30,
      natAdd 30 30 30,
      natConst 8 32,
      natAdd 38 30 8,
      natAdd 10 28 0,
      natAdd 12 22 0,
      natBranch 18 10 (o + 34) (o + 22),
      natLoad 8 12,
      natBranch 2 8 (o + 24) (o + 29),
      natLoad 8 10,
      natBranch 8 20 (o + 26) (o + 27),
      natBranch 20 8 (o + 29) (o + 27),
      natStore 38 2,
      jump (o + 30),
      natStore 38 0,
      natAdd 10 10 4,
      natAdd 12 12 4,
      natAdd 38 38 36,
      jump (o + 21),
      natAdd 0 26 32,
      natAdd 0 0 2,
      natAdd 8 30 36,
      natStore 8 8,
      natAdd 1 0 0,
      natAdd 1 1 1,
      natAdd 1 1 1,
      natAdd 1 1 1,
      natLoad 1 1,
      natBranch 0 1 (o + 48) (o + 44),
      natStore 0 1,
      natConst 1 1,
      natSub 0 0 1,
      jump (o + 38)])
    (n LVB BB cc : ℕ) (hLe : LVB % 2 = 0) (hB : BB % 2 = 1) (hL : 32 + 16 * n * n + 16 * n ≤ LVB)
    (M : ℕ → ℕ) (R : ℕ → ℝ) (h32 : M 32 = n) (h28 : M 28 = LVB) (h20 : M 20 = cc) (h22 : M 22 = BB) :
    ∃ τ, τ ≤ 26 * n + 29 ∧ (planarRAMRun p ⟨o, M, R⟩ τ).pc = o + 48 ∧
      (∀ j, j < n → (planarRAMRun p ⟨o, M, R⟩ τ).natMem (2 + n * n + j) = (if 1 ≤ M (BB + 2 * j) ∧ M (LVB + 2 * j) ≠ cc then 1 else 0)) :=
  OU.out_write p o hcode n LVB BB cc hLe hB hL M R h32 h28 h20 h22
