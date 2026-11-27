-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeSheetGram_proof_6a7cae3787a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:54:34.080088+00:00
-- url     : https://prove2.me/submissions/5e9f22ab-ac5a-48b9-9477-c66f4d92f327

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSheetGramLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeSheetGram
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gramVol_const_zero_81197df01573
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_succ_le_of_ringKrullDim_quotient_fb5ca6b44376
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_fibre_finite_20785c71949c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_coordBall_mass_6af667653fce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gramVol_nonneg_7dddc6a166b7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mul_setIntegral_eq_of_lintegral_5f5cb8ed0534


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
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ConeSheetGram
theorem _root_.solution (hL : ConeSheetGramLintegral.Statement) : ConeSheetGram.Statement := by
  intro n e h J ℓ A f hJ hdim hℓ hA hf
  obtain ⟨hb0, -⟩ := coordBall_mass (n := n) (m := e + 1) (succ_le_of_ringKrullDim_quotient J hdim)
  rw [mul_setIntegral_eq_of_lintegral (ν := volume) (fun y => IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y)
    (fun y x => WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y))
    (fun y x t => ‖t‖ ^ (2 * e) *
      gramVol (fun y' => (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y') y)
    (fun y x t => mul_nonneg (pow_nonneg (norm_nonneg t) _) (gramVol_nonneg _ y))
    (fun y x => (continuous_norm.pow _).mul continuous_const)
    (by positivity) hb0.ne' (fun F hF => hL n e h J ℓ A F hJ hdim hℓ hA hF) hf]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  unfold sheetSum
  refine finsum_congr fun x => finsum_congr fun _ => ?_
  unfold sheetThrough
  split_ifs with hs
  · rfl
  · simp [gramVol_const_zero]
end ConeSheetGram
end GroundTheory.Heights₂.Heights
