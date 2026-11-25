-- Prove2me | solution 1 for PI.SqPairLocal.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:24:07.443693+00:00
-- url     : https://prove2.me/submissions/f3a295b1-6fcd-4462-a11b-44245e63ff4e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Lemmata_GeneralBFactLeftBis_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_ExistsDenFg
import Theorems.Thm_Bl_general_b_fact_left_bis_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] {N : ℕ}
namespace PI.SqPairLocal
theorem _root_.solution (L'' : Submodule (𝓞 E) (Fin N → E))
    (hsp : Submodule.span E (L'' : Set (Fin N → E)) = ⊤) (v : Fin N → E) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ L'' := by
  first | exact Bl.general_b_fact_left_bis.goal1 .. | (apply Bl.general_b_fact_left_bis.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_bis.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_bis.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_bis.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_bis.goal1 <;> first | assumption | infer_instance)
end PI.SqPairLocal
