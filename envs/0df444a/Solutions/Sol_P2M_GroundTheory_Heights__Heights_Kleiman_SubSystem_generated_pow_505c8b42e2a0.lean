-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_generated_pow_505c8b42e2a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:31:09.643074+00:00
-- url     : https://prove2.me/submissions/e3b1b6a8-4c05-415e-8141-b4a2cf9fe51a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_generated_twist_3a4a44636f3f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_generated_twistSys_zero_69b6ba3803f8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace SubSystem
theorem _root_.solution {Q : SubSystem k x Ω} (hQ : Q.Generated) (n : ℕ) :
    (Q.pow n).Generated := by
  induction n with
  | zero => exact generated_twistSys_zero
  | succ n ih => exact SubSystem.generated_twist ih hQ
end SubSystem
end GroundTheory.Heights₂.Heights.Kleiman
