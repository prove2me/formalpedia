-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalizationPrimeDVR_hypotheses_inhabited_83f9663bf9a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:55:51.217696+00:00
-- url     : https://prove2.me/submissions/d1531857-fb13-4c00-88c8-93e24362b38b

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
namespace LocalizationPrimeDVR
theorem _root_.solution :
    (Ideal.span {(2 : ℤ)}).IsPrime ∧ Prime (2 : ℤ) :=
  ⟨(Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two, Int.prime_two⟩
end LocalizationPrimeDVR
end GroundTheory.Heights₂.Heights
