-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_algebraicIndependent_mk_X_iff_0a51e0acb677
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:48:20.21398+00:00
-- url     : https://prove2.me/submissions/066f8b9c-6294-4a1d-95d1-1c20cbadc364

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_aeval_mk_X_55c086bbd7ca

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution (I : Ideal (MvPolynomial (Fin n) ℂ)) (u : Set (Fin n)) :
    AlgebraicIndependent ℂ (fun i : u => Ideal.Quotient.mk I (X (i : Fin n))) ↔
      ∀ q : MvPolynomial u ℂ, rename Subtype.val q ∈ I → q = 0 := by
  rw [algebraicIndependent_iff]
  simp only [aeval_mk_X, Ideal.Quotient.eq_zero_iff_mem]
end GroundTheory.Heights₂.Heights.ComplexSets
