-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_aeval_mk_X_55c086bbd7ca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:10:34.866041+00:00
-- url     : https://prove2.me/submissions/bd89aafe-42cb-4355-bdc3-901fa7f432c4

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim

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
theorem _root_.solution (I : Ideal (MvPolynomial (Fin n) ℂ)) (u : Set (Fin n))
    (q : MvPolynomial u ℂ) :
    aeval (fun i : u => Ideal.Quotient.mk I (X (i : Fin n))) q =
      Ideal.Quotient.mk I (rename Subtype.val q) := by
  induction q using MvPolynomial.induction_on with
  | C a => rw [aeval_C, rename_C]; rfl
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]
end GroundTheory.Heights₂.Heights.ComplexSets
