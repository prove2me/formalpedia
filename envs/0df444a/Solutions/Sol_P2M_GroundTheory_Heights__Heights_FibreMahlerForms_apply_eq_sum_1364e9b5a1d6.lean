-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FibreMahlerForms_apply_eq_sum_1364e9b5a1d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:46:02.19962+00:00
-- url     : https://prove2.me/submissions/03f2813c-4c7f-47ec-8eab-d41c7d30907d

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
theorem _root_.solution (b : OrthonormalBasis ι ℂ V) (ℓ : V →ₗ[ℂ] ℂ) (ξ : V) :
    ℓ ξ = ∑ j, inner ℂ (b j) ξ * ℓ (b j) := by
  conv_lhs => rw [← b.sum_repr' ξ]
  simp only [map_sum, map_smul, smul_eq_mul]
end GroundTheory.Heights₂.Heights.FibreMahlerForms
