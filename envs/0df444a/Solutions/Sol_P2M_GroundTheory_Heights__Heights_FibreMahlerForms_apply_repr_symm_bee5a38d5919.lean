-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FibreMahlerForms_apply_repr_symm_bee5a38d5919
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:41:44.899682+00:00
-- url     : https://prove2.me/submissions/135e4828-8de7-4c49-adc2-cca2b69a8fbd

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
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι]
namespace GroundTheory.Heights₂.Heights.FibreMahlerForms
theorem _root_.solution (b : OrthonormalBasis ι ℂ V) (ℓ : V →ₗ[ℂ] ℂ) (v : ι → ℂ) :
    ℓ (b.repr.symm (WithLp.toLp 2 v)) = ∑ j, ℓ (b j) * v j := by
  rw [← b.sum_repr_symm]
  simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
end GroundTheory.Heights₂.Heights.FibreMahlerForms
