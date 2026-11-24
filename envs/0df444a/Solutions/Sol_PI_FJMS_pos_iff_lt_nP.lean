-- Prove2me | solution 1 for PI.FJMS.pos_iff_lt_nP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:48.011+00:00
-- url     : https://prove2.me/submissions/f23f726f-e1aa-48a5-9a1e-01d9ac1e3190

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Lemmata_B1959r_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PosIffLtNP
import Theorems.Thm_Bl_general_b_fact_upper_bis_form_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMS
open PI.FJM PI.FJMP
namespace PI.FJMS
theorem _root_.solution {n : ℕ} (f : Fin n → ℚ) (hseg : ∀ i i' : Fin n, i < i' → 0 < f i' → 0 < f i)
    (i : Fin n) : 0 < f i ↔ i.val < nP f := by
  first | exact Bl.general_b_fact_upper_bis_form.goal1 .. | (apply Bl.general_b_fact_upper_bis_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_upper_bis_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_bis_form.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_upper_bis_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_bis_form.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_upper_bis_form.goal1 n f hseg i | exact @Bl.general_b_fact_upper_bis_form.goal1 n f hseg | exact @Bl.general_b_fact_upper_bis_form.goal1 n f | exact @Bl.general_b_fact_upper_bis_form.goal1 n
end PI.FJMS
