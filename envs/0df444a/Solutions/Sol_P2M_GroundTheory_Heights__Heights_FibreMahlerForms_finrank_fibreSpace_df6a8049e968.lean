-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FibreMahlerForms_finrank_fibreSpace_df6a8049e968
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:46:09.06747+00:00
-- url     : https://prove2.me/submissions/1a29b3de-71e9-48ed-92b8-728751393ed6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsFibreMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PDiagonalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PFibreMahlerForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_span_fibreVec_eq_top_3f80ac305458


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
open MvPolynomial NumberField TensorProduct ComplexAt
noncomputable section
open GroundTheory.Heights₂.Heights.FibreMahlerForms
variable {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (𝓞 F) W]
  [Module.Finite (𝓞 F) W] [Module.Projective (𝓞 F) W]
namespace GroundTheory.Heights₂.Heights.FibreMahlerForms
theorem _root_.solution (h : HermitianMetric F W) (σ : F →+* ℂ) :
    Module.finrank ℂ (FibreSpace h σ) = Module.finrank (𝓞 F) W := by
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := F) (E := W)
  let b := Module.Basis.mk (linearIndependent_fibreVec h σ hs)
    (LatticeLemmas.span_fibreVec_eq_top h σ hs (Fintype.card_fin _)).ge
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
end GroundTheory.Heights₂.Heights.FibreMahlerForms
