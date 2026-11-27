-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.lineSection_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:24:45.185709+00:00
-- url     : https://prove2.me/submissions/744e4c97-16c0-43dd-8b07-77ab2ea4b105

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_Inhabit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_single_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inhV_relevant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inhV_singleton
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_divCycle_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_divCycle_prime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_homog_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_homog_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution (F : Type*) [Field F] : LineSectionStatement F := by
  have hQ : (Ideal.span {X ⟨(), 0⟩} : Ideal (MRingOver F fun _ : Unit => Fin 2)).IsPrime := by
    rw [← inhV_singleton]; infer_instance
  have hrel : IsRelevant (Ideal.span {X ⟨(), 0⟩} : Ideal (MRingOver F fun _ : Unit => Fin 2)) := by
    rw [← inhV_singleton]; exact inhV_relevant _ (by decide)
  refine ⟨⟨fun _ => 1, 0, ?_, inh_homog_one, ?_, ?_, fun _ => by simp⟩, ?_⟩
  · simpa [inh_single_unit] using inh_homog_X (F := F) (⟨(), 0⟩ : Σ _ : Unit, Fin 2)
  · rw [Ideal.mem_bot]; exact X_ne_zero _
  · rw [Ideal.mem_bot]; exact one_ne_zero
  · rw [ratDiv, inh_divCycle_prime ⊥ _ _ (bot_sup_eq _) hrel, inh_divCycle_one]
    simp
end ReciprocityTheory.ChartRestriction.G.AI.I1
