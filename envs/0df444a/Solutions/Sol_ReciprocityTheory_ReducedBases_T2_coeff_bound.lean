-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.coeff_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:15:41.309294+00:00
-- url     : https://prove2.me/submissions/a8c5e3c2-96c6-403b-bb29-94de742516e4

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsBoundedBasis
import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_nu_split
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_filter_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution (b : Fin d → E) (hb : LinearIndependent ℝ b)
    (hs : ∀ i j : Fin d, j < i → |mu b i j| ≤ 1 / 2) (c : Fin d → ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ j, |nu b c j| ≤ M) (j : Fin d) : |c j| ≤ (3 / 2) ^ d * M := by
  have key : ∀ j : Fin d, |c j| ≤ M + 1 / 2 * ∑ l ∈ univ.filter (fun l : Fin d => j.val + 1 ≤ l.val), |c l| := by
    intro j
    have e := nu_split b hb c j
    have h1 : |∑ l ∈ univ.filter (fun l : Fin d => j.val + 1 ≤ l.val), c l * mu b l j| ≤
        1 / 2 * ∑ l ∈ univ.filter (fun l : Fin d => j.val + 1 ≤ l.val), |c l| := by
      rw [Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l hl => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hs l j (Fin.lt_iff_val_lt_val.mpr (by omega))) (abs_nonneg _)
    have h2 := abs_le.mp (hM j)
    have h1' := abs_le.mp h1
    rw [abs_le]
    constructor <;> linarith
  have T : ∀ m : ℕ, ∀ k : ℕ, d = k + m →
      M + 1 / 2 * ∑ l ∈ univ.filter (fun l : Fin d => k ≤ l.val), |c l| ≤ (3 / 2) ^ m * M := by
    intro m
    induction m with
    | zero =>
      intro k hk
      have he : univ.filter (fun l : Fin d => k ≤ l.val) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro l _
        have := l.isLt
        omega
      rw [he, Finset.sum_empty]
      simp
    | succ m ih =>
      intro k hk
      have hkd : k < d := by omega
      rw [filter_ge k hkd, Finset.sum_insert (by simp)]
      have h1 := ih (k + 1) (by omega)
      have h2 : |c ⟨k, hkd⟩| ≤ M + 1 / 2 * ∑ l ∈ univ.filter (fun l : Fin d => k + 1 ≤ l.val), |c l| :=
        key ⟨k, hkd⟩
      rw [pow_succ]
      linarith
  have hj := key j
  have hjd := j.isLt
  have h3 := T (d - (j.val + 1)) (j.val + 1) (by omega)
  have hp : ((3 : ℝ) / 2) ^ (d - (j.val + 1)) ≤ (3 / 2) ^ d := by
    first
    | exact pow_le_pow_right₀ (by norm_num) (by omega)
    | exact pow_le_pow_right (by norm_num) (by omega)
  have hM' := mul_le_mul_of_nonneg_right hp hM0
  linarith
end ReciprocityTheory.ReducedBases.T2
