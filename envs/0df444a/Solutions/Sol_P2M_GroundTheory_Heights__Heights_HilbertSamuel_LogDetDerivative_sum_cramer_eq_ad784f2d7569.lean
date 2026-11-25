-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_LogDetDerivative_sum_cramer_eq_ad784f2d7569
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:42.130074+00:00
-- url     : https://prove2.me/submissions/5e56af0e-a9e1-487b-aee8-a93277159df7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StandardLatticeVecIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_HasDerivAtDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Matrix Equiv
open scoped ComplexOrder
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace LogDetDerivative
theorem _root_.solution {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ)
    (hA : IsUnit A.det) :
    ∑ i, A.cramer (fun k ↦ B k i) i = A.det * (A⁻¹ * B).trace := by
  simp only [← det_smul_inv_mulVec_eq_cramer A _ hA, Pi.smul_apply, smul_eq_mul, trace,
    diag_apply, mul_apply, mulVec, dotProduct, Finset.mul_sum]
end LogDetDerivative
end GroundTheory.Heights₂.Heights.HilbertSamuel
