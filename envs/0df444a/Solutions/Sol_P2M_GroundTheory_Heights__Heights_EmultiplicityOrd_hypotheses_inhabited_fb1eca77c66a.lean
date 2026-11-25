-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EmultiplicityOrd_hypotheses_inhabited_fb1eca77c66a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:54:37.84522+00:00
-- url     : https://prove2.me/submissions/fd7a11b5-9690-4e17-bd5f-58f5a0a6252a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder

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
open MvPolynomial
noncomputable section
open LineChowForm
namespace GroundTheory.Heights₂.Heights
namespace EmultiplicityOrd
theorem _root_.solution :
    (Ideal.span {(2 : ℤ)}).IsPrime ∧ Prime (2 : ℤ) ∧ (4 : ℤ) ≠ 0 :=
  ⟨(Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two, Int.prime_two, by norm_num⟩
end EmultiplicityOrd
end GroundTheory.Heights₂.Heights
