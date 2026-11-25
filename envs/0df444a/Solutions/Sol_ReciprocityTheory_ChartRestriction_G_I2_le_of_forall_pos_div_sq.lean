-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.le_of_forall_pos_div_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:31:11.922286+00:00
-- url     : https://prove2.me/submissions/8b854148-0f16-4cb4-9f92-23bdd6777b3c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitO
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitG
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_soPsi_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.soPsi_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {a c S : ℝ} (ha : 0 < a) (hc : 0 < c) (h : ∀ ε > 0, c / (a + ε) ^ 2 ≤ S) :
    c / a ^ 2 ≤ S := by
  have hcont : ContinuousAt (fun ε : ℝ => c / (a + ε) ^ 2) 0 := by
    apply ContinuousAt.div continuousAt_const
    · exact ((continuous_const.add continuous_id).pow 2).continuousAt
    · simpa using ha.ne'
  have ht : Filter.Tendsto (fun ε : ℝ => c / (a + ε) ^ 2) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (c / a ^ 2)) := by
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using this
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε using h ε hε
end ReciprocityTheory.ChartRestriction.G.I2
