-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_sT_ne_zero_d0219b53b8a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:23:00.5723+00:00
-- url     : https://prove2.me/submissions/ee6d105b-76c4-42cf-9692-fc969f4683ad

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
namespace GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
theorem _root_.solution (j : Fin n) (hj : genPt Q j ≠ 0) : sT Q e ≠ 0 := by
  intro h
  have h' := congrArg (eval (Pi.single j 1)) h
  simp [sT, Pi.single_apply] at h'
  exact hj h'
end GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
