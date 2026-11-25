-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain___X_inr_ff9d3e0fb1c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:23:17.674537+00:00
-- url     : https://prove2.me/submissions/0d8b7959-2af8-4cb3-921a-bea80c083f13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
variable {k : Type} [Field k] {n : ℕ}
variable (Q : Ideal (MvPolynomial (Fin n) k)) [Q.IsPrime] (e : ℕ)
omit [Q.IsPrime]
namespace GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
theorem _root_.solution (c : Fin n → Fn Q) (j : Fin n) : ρ Q e c (X (.inr j)) = X j := by
  simp [ρ, gsub, sumAlgEquiv_X_inl]
end GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
