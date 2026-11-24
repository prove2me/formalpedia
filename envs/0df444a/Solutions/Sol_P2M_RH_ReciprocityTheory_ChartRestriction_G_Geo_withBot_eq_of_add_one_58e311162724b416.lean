-- Prove2me | solution 1 for P2M_RH_ReciprocityTheory_ChartRestriction_G_Geo_withBot_eq_of_add_one_58e311162724b416
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:43.149787+00:00
-- url     : https://prove2.me/submissions/d6171c97-e62f-4445-b1fc-ff70795f76c1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppA
import Definitions.Def_Lemmata_GeneralBFactTerForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Theorems.Thm_Bl_general_b_fact_rest_goal1
import Theorems.Thm_Bl_general_b_fact_side_goal1
import Theorems.Thm_Bl_general_b_fact_ter_form_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable {σ : Type*} [Finite σ]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {x : WithBot ℕ∞} {m : ℕ} (h : x + 1 = ((m + 1 : ℕ) : WithBot ℕ∞)) :
    x = (m : WithBot ℕ∞) := by
  first | exact Bl.general_b_fact_ter_form.goal1 .. | (apply Bl.general_b_fact_ter_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_ter_form.goal1 <;> assumption)
end ReciprocityTheory.ChartRestriction.G.Geo
