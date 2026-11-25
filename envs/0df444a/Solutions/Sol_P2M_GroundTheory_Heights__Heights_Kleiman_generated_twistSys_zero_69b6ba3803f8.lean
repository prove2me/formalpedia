-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_generated_twistSys_zero_69b6ba3803f8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:21:14.937868+00:00
-- url     : https://prove2.me/submissions/affd941a-58ff-4052-a8db-5ef8e42e8b7b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_zero_eq_one_5ef25f86ec85
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_span_secs_le_b24ff46a355a

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
theorem _root_.solution : (twistSys k x 0).Generated := by
  intro I
  apply le_antisymm (SubSystem.span_secs_le _ I)
  change twistMod k x 0 I ≤ _
  rw [twistMod_zero_eq_one, Submodule.one_eq_span]
  apply Submodule.span_mono
  rintro _ rfl
  exact (Submodule.mem_iInf _).mpr fun J => one_mem_twistMod_zero J
end GroundTheory.Heights₂.Heights.Kleiman
