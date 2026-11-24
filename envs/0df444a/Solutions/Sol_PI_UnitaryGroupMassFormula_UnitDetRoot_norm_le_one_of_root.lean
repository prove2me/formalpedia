-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.norm_le_one_of_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:30:27.770809+00:00
-- url     : https://prove2.me/submissions/a626b4e5-ce2c-4d1e-bf8a-db6daf0f724b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Lemmata_GeneralBFactLeftTer_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NormLeOneOfRoot
import Theorems.Thm_Bl_general_b_fact_left_ter_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution {F : Type*} [NormedField F] [IsUltrametricDist F] {y : F}
    (p : Polynomial ℤ) (hp : p.Monic) (hpy : p.eval₂ (Int.castRingHom F) y = 0) : ‖y‖ ≤ 1 := by
  first | exact Bl.general_b_fact_left_ter.goal1 .. | (apply Bl.general_b_fact_left_ter.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_ter.goal1 <;> assumption)
end PI.UnitaryGroupMassFormula.UnitDetRoot
