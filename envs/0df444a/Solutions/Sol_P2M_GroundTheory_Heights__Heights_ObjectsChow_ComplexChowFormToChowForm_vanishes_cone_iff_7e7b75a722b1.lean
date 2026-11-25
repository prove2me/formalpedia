-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_ComplexChowFormToChowForm_vanishes_cone_iff_7e7b75a722b1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:35.810601+00:00
-- url     : https://prove2.me/submissions/04f1ca57-6624-4d53-ab8a-2ec12b700771

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRadicalBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_AevalGenericIdealIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_ComplexChowFormToChowForm_aeval_genericIdeal_iff_fb99c4bb003f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coeff_coordPoly_539797cde10d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_C_mul_map_9d8219af7fc0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_mem_of_mem_map_75eab8a0118b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_sum_8ff9631ad41f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_incidenceIdeal_map_8d93a5362789
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_mem_zeroLocus_incidenceIdeal_a3506a649f6c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_radical_map_eq_9ece7ec07417
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_sum_coordPoly_903079f12110
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_vanishes_incidence_iff_796d408552b0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk conePts)
open ChowFormExtend (incidenceIdeal coordPoly coeff_coordPoly coordPoly_C_mul_map coordPoly_mem_of_mem_map
  mem_zeroLocus_incidenceIdeal vanishes_incidence_iff incidenceIdeal_map radical_map_eq coordSupport
  sum_coordPoly coordPoly_sum)
open GroundTheory.Heights₂.Heights.ObjectsChow.ComplexChowFormToChowForm
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsChow.ComplexChowFormToChowForm
theorem _root_.solution {k : ℕ} (P : Ideal (MRing (PBlk n))) (p : MvPolynomial (Fin k × Fin n) ℂ) :
    (∀ v : Fin k × Fin n → ℂ, (∃ z ∈ conePts (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P),
        ∀ i, ∑ j, v (i, j) * z j = 0) → eval v p = 0) ↔
      ∀ j, X (Sum.inr j) * rename Sum.inl p ∈
        (incidenceIdeal ((genericIdeal P).map (map (algebraMap ℚ ℂ))) k).radical := by
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
  simp only [mem_vanishingIdeal_iff, mem_zeroLocus_incidenceIdeal, aeval_genericIdeal_iff]
  constructor
  · rintro h j z ⟨hI, hlin⟩
    rw [map_mul, aeval_X, aeval_rename]
    by_cases hx : z ∘ Sum.inr = 0
    · rw [show z (Sum.inr j) = 0 from congrFun hx j, zero_mul]
    · rw [aeval_eq_eval, h (z ∘ Sum.inl) ⟨z ∘ Sum.inr, ⟨hx, hI⟩, hlin⟩, mul_zero]
  · rintro h v ⟨x, ⟨hx, hI⟩, hlin⟩
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.1 hx
    have := h j (Sum.elim v x) ⟨by simpa using hI, by simpa using hlin⟩
    rw [map_mul, aeval_X, aeval_rename, aeval_eq_eval] at this
    simpa [hj] using this
end GroundTheory.Heights₂.Heights.ObjectsChow.ComplexChowFormToChowForm
