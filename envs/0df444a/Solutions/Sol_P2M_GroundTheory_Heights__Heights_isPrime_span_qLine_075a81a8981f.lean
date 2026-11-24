-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isPrime_span_qLine_075a81a8981f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:15.375616+00:00
-- url     : https://prove2.me/submissions/2313841c-64bf-4212-b4e1-a4ac0b46bed9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_prime_qLine_c53c4192a86d

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
theorem _root_.solution : (Ideal.span {qLine}).IsPrime :=
  (Ideal.span_singleton_prime prime_qLine.ne_zero).mpr prime_qLine
end GroundTheory.Heights₂.Heights
