-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain___injective_9eafdcb1cad6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:22:53.024415+00:00
-- url     : https://prove2.me/submissions/2232b7eb-cb91-4d66-8318-8e53db516427

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
theorem _root_.solution (c : Fin n → Fn Q) (h : Function.Injective (gsub Q e c)) :
    Function.Injective (ρ Q e c) :=
  (MvPolynomial.map_injective _ h).comp
    ((sumAlgEquiv k (Fin n) (Fin e × Fin n)).injective.comp
      (renameEquiv k (Equiv.sumComm (Fin e × Fin n) (Fin n))).injective)
end GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
