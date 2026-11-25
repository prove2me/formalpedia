-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FibreMahlerForms_archLin_fibreGen_25cb1cf05c25
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:47:31.756697+00:00
-- url     : https://prove2.me/submissions/2651e6c3-0a58-47ec-9f8a-f08067979a3d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsFibreMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PDiagonalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PFibreMahlerForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_archLin_fibreVec_3b5dbbaf6e5b

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
theorem _root_.solution (h : HermitianMetric F W) (τ : K →+* ℂ) (yv : DualVec F W K) {n : ℕ}
    (w : Fin n → W) (x : Fin n → ℂ) :
    archLin h τ yv (fibreGen h (τ.comp (algebraMap F K)) w x) = ∑ k, τ (yv (w k)) * x k := by
  simp only [fibreGen, map_sum, map_smul, archLin_fibreVec, smul_eq_mul, mul_comm]
end GroundTheory.Heights₂.Heights.FibreMahlerForms
