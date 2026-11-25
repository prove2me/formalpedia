-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeFibreAverage_hypotheses_inhabited_8e8ca043c905
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:52:58.61054+00:00
-- url     : https://prove2.me/submissions/23200b3c-6811-44ee-8c2c-fca28879c3f0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSectionVertical_hypotheses_inhabited_25f0794614ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSection_hypotheses_inhabited_b7e6b352f62b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSwap_hypotheses_inhabited_286c010aa601
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightLowerBound_hypotheses_inhabited_32f5e648d58c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightMul_hypotheses_inhabited_0cc03fe7f1d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightRecursion_hypotheses_inhabited_a59b12a05d49
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFibreDegree_hypotheses_inhabited_7d66142c3999
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMassOfFibre_hypotheses_inhabited_77106a6e7ffc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerMul_hypotheses_inhabited_95e2ae5d82a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerSection_hypotheses_inhabited_066629c10381
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanLinear_hypotheses_inhabited_1fdf021d66be


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
open MvPolynomial MeasureTheory
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ConeFibreAverage
theorem _root_.solution :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
      ∀ᵐ π : Fin 1 → Fin 1 → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin 1),
        fibreCount (HermNorm.std 1) ⊥ π w ≠ ⊤ := by
  obtain ⟨hJ, hfib⟩ := ConeMassOfFibre.hypotheses_inhabited
  refine ⟨hJ, ?_⟩
  filter_upwards [hfib] with π hπ
  filter_upwards [hπ] with w hw
  rw [hw]
  exact ENat.natCast_ne_top 1
end ConeFibreAverage
end GroundTheory.Heights₂.Heights
