-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.inK_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:07:15.592525+00:00
-- url     : https://prove2.me/submissions/5dcf8b76-d508-4493-bbee-68aade84bc08

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFactsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : inK ε Y ↔ Yᴴ = -Y ∧ IsBlock ε Y := by
  unfold inK IsBlock inG
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hcomm : Y * Jm ε = Jm ε * Y ↔ ∀ a b, ε a ≠ ε b → Y a b = 0 := by
    constructor
    · intro h a b hab
      have h1 := congrFun (congrFun h a) b
      simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
      have hdb : (if ε b then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
      have hda : (if ε a then (1 : ℂ) else -1) = -(if ε b then (1 : ℂ) else -1) := by
        cases ha : ε a <;> cases hb : ε b <;> simp_all
      rw [hda] at h1
      have h5 : 2 * (Y a b * (if ε b then (1 : ℂ) else -1)) = 0 := by linear_combination h1
      exact (mul_eq_zero.mp ((mul_eq_zero.mp h5).resolve_left two_ne_zero)).resolve_right hdb
    · intro h
      ext a b
      simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases hab : ε a = ε b
      · rw [hab]
        ring
      · rw [h a b hab]
        ring
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, hcomm.mp h2⟩
    have h3 : Yᴴ * Jm ε = -(Y * Jm ε) := by
      rw [h2]
      exact eq_neg_of_add_eq_zero_left h1
    calc Yᴴ = Yᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = -(Y * Jm ε) * Jm ε := by rw [h3]
      _ = -Y := by rw [Matrix.neg_mul, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  · rintro ⟨h1, h2⟩
    have h4 := hcomm.mpr h2
    refine ⟨?_, h4⟩
    rw [h1, Matrix.neg_mul, h4, neg_add_cancel]
end ReciprocityTheory.ChartRestriction.DS.S7
