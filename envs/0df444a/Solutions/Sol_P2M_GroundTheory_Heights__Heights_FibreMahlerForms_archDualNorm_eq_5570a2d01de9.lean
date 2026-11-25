-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FibreMahlerForms_archDualNorm_eq_5570a2d01de9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:05:36.054628+00:00
-- url     : https://prove2.me/submissions/7c3b4d1a-4e43-4bd2-a19d-0ab132f1a66a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsFibreMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PDiagonalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PFibreMahlerForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_iSup_norm_ball_b20791a9192b

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
theorem _root_.solution (h : HermitianMetric F W) (τ : K →+* ℂ) (yv : DualVec F W K) {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℂ (FibreSpace h (τ.comp (algebraMap F K)))) :
    archDualNorm h τ yv = √(∑ j, ‖archLin h τ yv (b j)‖ ^ 2) :=
  iSup_norm_ball b (archLin h τ yv)
end GroundTheory.Heights₂.Heights.FibreMahlerForms
