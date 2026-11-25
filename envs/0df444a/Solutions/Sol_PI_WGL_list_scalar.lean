-- Prove2me | solution 1 for PI.WGL.list_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:17:47.275811+00:00
-- url     : https://prove2.me/submissions/b79f2f57-d525-415e-bfd1-7849a934d0c0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliShift
import Definitions.Def_Lemmata_GeneralBFactRight_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliZ
import Theorems.Thm_Bl_general_b_fact_right_goal1
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL
theorem _root_.solution {V ι : Type*} [AddCommGroup V] [Module ℂ V] (L : List ι) (F : ι → Module.End ℂ V)
    (c : ι → ℂ) (x : V) (hL : ∀ j ∈ L, F j x = c j • x) : (L.map F).prod x = (L.map c).prod • x := by
  first | exact Bl.general_b_fact_right.goal1 .. | (apply Bl.general_b_fact_right.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right.goal1 <;> assumption) | (apply @Bl.general_b_fact_right.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right.goal1 <;> assumption) | (apply @Bl.general_b_fact_right.goal1 <;> first | assumption | infer_instance)
end PI.WGL
