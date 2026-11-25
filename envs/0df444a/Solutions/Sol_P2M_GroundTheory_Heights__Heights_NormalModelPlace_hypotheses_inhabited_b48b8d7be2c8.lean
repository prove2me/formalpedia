-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalModelPlace_hypotheses_inhabited_b48b8d7be2c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:31:38.41582+00:00
-- url     : https://prove2.me/submissions/d0e0321e-2d97-4eb3-a10d-d1aff65473b6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_const_mem_zeroSetIn_lineDiagonal_f0d6d4f27065


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
variable {σ : Type*}
namespace GroundTheory.Heights₂.Heights
namespace NormalModelPlace
theorem _root_.solution :
    (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)).IsPrime ∧
      (fun _ ↦ 0 : Fin 1 ⊕ Fin IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalModel.m → ℂ) ∈
        IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalModel.ideal ∧
      IndefiniteRowSideFullHecke.ComplexSets.firstCoords (fun _ ↦ 0 : Fin 1 ⊕ Fin IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalModel.m → ℂ) = 0 :=
  ⟨Ideal.isPrime_bot, IndefiniteRowSideFullHecke.ComplexSets.const_mem_zeroSetIn_lineDiagonal 0, rfl⟩
end NormalModelPlace
end GroundTheory.Heights₂.Heights
