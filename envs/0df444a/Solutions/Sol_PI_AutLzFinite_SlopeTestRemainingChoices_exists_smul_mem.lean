-- Prove2me | solution 1 for PI.AutLzFinite.SlopeTestRemainingChoices.exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:35:03.011581+00:00
-- url     : https://prove2.me/submissions/b72a4191-f5b1-4b03-b120-0bfaca1b489e

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MjSmulRight
import Definitions.Def_Lemmata_GeneralBFactThirdExtra_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_FiniteOfIntegralBound
import Theorems.Thm_Bl_general_b_fact_third_extra_goal1
import Theorems.Thm_Bl_general_b_fact_upper_alt_form_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AutLzFinite PI.AutLzFinite.SlopeTestRemainingChoices
open Formalism.BasicNotions NumberField
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}
namespace PI.AutLzFinite.SlopeTestRemainingChoices
theorem _root_.solution (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.span E (Λ : Set S.V) = ⊤) (v : S.V) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ := by
  first | exact Bl.general_b_fact_third_extra.goal1 .. | (apply Bl.general_b_fact_third_extra.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third_extra.goal1 <;> assumption) | (apply @Bl.general_b_fact_third_extra.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_third_extra.goal1 <;> assumption) | (apply @Bl.general_b_fact_third_extra.goal1 <;> first | assumption | infer_instance)
end PI.AutLzFinite.SlopeTestRemainingChoices
