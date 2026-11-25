-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_solveMap_gen_3170fbd5da3a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:16:27.187024+00:00
-- url     : https://prove2.me/submissions/f76e24de-9379-4e18-a2a2-efc26be7a5a8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBundleRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceBundleRadicalAway
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_coeffMap_comp_mapC_04b3d0cca687

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SliceBundleRadicalAway
variable {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) (q : Fin n → ℂ) (k : Fin n)
namespace GroundTheory.Heights₂.Heights.SliceBundleRadicalAway
theorem _root_.solution (i : Fin d) :
    solveMap J d q k (∑ j, C (X (i, j)) * (X j - C (C (q j)))) = 0 := by
  have h : ∀ j, solveMap J d q k (C (X (i, j)) * (X j - C (C (q j)))) =
      (X (i, j) - if j = k then
        C (IsLocalization.Away.invSelf (Ideal.Quotient.mk J (X k - C (q k)))) * rowForm J d q k i
      else 0) * C (toBase J q k (X j - C (q j))) := by
    intro j
    have := RingHom.congr_fun (coeffMap_comp_mapC J d q k) (X j - C (q j))
    have e : MvPolynomial.map (C : ℂ →+* MvPolynomial (Fin d × Fin n) ℂ) (X j - C (q j)) =
        X j - C (C (q j)) := by simp
    rw [RingHom.comp_apply, RingHom.comp_apply, e] at this
    rw [map_mul, this]
    congr 1
    rw [solveMap, eval₂Hom_C, coeffMap, eval₂Hom_X']
  rw [map_sum, Finset.sum_congr rfl fun j _ => h j]
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [← rowForm, mul_assoc, mul_comm (rowForm J d q k i), ← mul_assoc, ← map_mul]
  have hu : IsLocalization.Away.invSelf (Ideal.Quotient.mk J (X k - C (q k))) *
      toBase J q k (X k - C (q k)) = (1 : Base J q k) := by
    rw [mul_comm]
    exact IsLocalization.Away.mul_invSelf (S := Base J q k) (Ideal.Quotient.mk J (X k - C (q k)))
  rw [hu, map_one, one_mul, sub_self]
end GroundTheory.Heights₂.Heights.SliceBundleRadicalAway
