-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.exists_common
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:35:24.746082+00:00
-- url     : https://prove2.me/submissions/82f2c6a7-0ae0-4552-a2b8-334aa3c7ea23

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_SkewApprox
import Definitions.Def_Lemmata_GeneralBFactRightTer_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_Assembly
import Theorems.Thm_Bl_general_b_fact_right_ter_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open PI PI.UnitaryApproxFinWork
namespace PI.UnitaryApproxFinWork
theorem _root_.solution {F : Type} [Field F] [NumberField F] {ι : Type} (s : Finset ι)
    (Q : ι → 𝓞 F → Prop) (hQ : ∀ i c r, Q i c → Q i (c * r)) (h : ∀ i ∈ s, ∃ c, c ≠ 0 ∧ Q i c) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i ∈ s, Q i c := by
  first | exact Bl.general_b_fact_right_ter.goal1 .. | (apply Bl.general_b_fact_right_ter.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_ter.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_ter.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_ter.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_ter.goal1 <;> first | assumption | infer_instance)
end PI.UnitaryApproxFinWork
