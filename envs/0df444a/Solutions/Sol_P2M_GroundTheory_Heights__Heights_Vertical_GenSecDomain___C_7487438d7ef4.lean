-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain___C_7487438d7ef4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:23:13.386782+00:00
-- url     : https://prove2.me/submissions/0f85dcc9-80e7-4a97-b6e8-b3154bf38a0b

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
theorem _root_.solution (c : Fin n → Fn Q) (a : k) : ρ Q e c (C a) = C (C (algebraMap k (Fn Q) a)) := by
  simp [ρ, gsub, sumAlgEquiv_C_inl]
end GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
