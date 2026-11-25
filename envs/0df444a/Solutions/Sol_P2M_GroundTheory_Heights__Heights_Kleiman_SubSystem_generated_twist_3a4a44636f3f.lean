-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_generated_twist_3a4a44636f3f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:16:03.835797+00:00
-- url     : https://prove2.me/submissions/92319e58-a350-4041-8407-7716d657da49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_sub_eq_mul_d7e23ae652ec
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
namespace SubSystem
theorem _root_.solution {F Q : SubSystem k x Ω} (hF : F.Generated) (hQ : Q.Generated) :
    (F.twist Q).Generated := by
  intro I
  apply le_antisymm (SubSystem.span_secs_le _ I)
  rw [SubSystem.twist_sub_eq_mul, ← hF I, ← hQ I, Submodule.span_mul_span]
  apply Submodule.span_mono
  rintro _ ⟨a, ha, b, hb, rfl⟩
  refine (Submodule.mem_iInf _).mpr fun J => ?_
  change a * b ∈ (F.twist Q).sub J
  rw [SubSystem.twist_sub_eq_mul]
  exact Submodule.mul_mem_mul ((Submodule.mem_iInf _).mp ha J) ((Submodule.mem_iInf _).mp hb J)
end SubSystem
end GroundTheory.Heights₂.Heights.Kleiman
