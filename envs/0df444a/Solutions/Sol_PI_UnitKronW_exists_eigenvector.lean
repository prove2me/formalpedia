-- Prove2me | solution 1 for PI.UnitKronW.exists_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:33:54.857053+00:00
-- url     : https://prove2.me/submissions/8b8cf67f-d579-40ad-ae23-7337343e2d33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_Development
import Definitions.Def_Lemmata_GeneralBFactRightBis_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_PosDefFormNeZero
import Theorems.Thm_Bl_general_b_fact_right_bis_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitKronW
open Matrix Polynomial ComplexOrder
namespace PI.UnitKronW
theorem _root_.solution {k : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (μ : ℂ) (hμ : G.charpoly.IsRoot μ) :
    ∃ v : Fin k → ℂ, v ≠ 0 ∧ G *ᵥ v = μ • v := by
  first | exact Bl.general_b_fact_right_bis.goal1 .. | (apply Bl.general_b_fact_right_bis.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_bis.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_bis.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_bis.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_bis.goal1 <;> first | assumption | infer_instance)
end PI.UnitKronW
