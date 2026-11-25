-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FibreMahlerForms_archLin_fibreVec_3b5dbbaf6e5b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:41:07.190876+00:00
-- url     : https://prove2.me/submissions/dfe9f7cb-cee3-4d67-8b17-d3d7e49abda9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsFibreMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PDiagonalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PFibreMahlerForms

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
variable {K : Type} [Field K] [NumberField K] [Algebra F K]
namespace GroundTheory.Heights₂.Heights.FibreMahlerForms
theorem _root_.solution (h : HermitianMetric F W) (τ : K →+* ℂ) (yv : DualVec F W K) (e : W) :
    archLin h τ yv (fibreVec h (τ.comp (algebraMap F K)) e) = τ (yv e) := by
  simp only [archLin, LinearMap.coe_mk, AddHom.coe_mk, fibreVec, LinearEquiv.symm_apply_apply,
    archFunctional, TensorProduct.lift.tmul, LinearMap.mk₂_apply, one_mul,
    AlgEquiv.symm_apply_apply]
end GroundTheory.Heights₂.Heights.FibreMahlerForms
