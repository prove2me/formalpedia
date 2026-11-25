-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.pushA_piece_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:52.845237+00:00
-- url     : https://prove2.me/submissions/0030377d-0f66-4375-bdd4-44fa6408ae72

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
import Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_fib

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (q : X → Fin e → ℂ) (s : (Fin e → ℂ) → X) {D : Set (Fin e → ℂ)}
    (hinj : Set.InjOn (q ∘ s) D) (k : X → ℝ) (y : Fin e → ℂ) :
    ‖∑ᶠ x ∈ q ⁻¹' {y} ∩ s '' D, k x‖ = ∑ᶠ x ∈ q ⁻¹' {y} ∩ s '' D, |k x| := by
  obtain ⟨h1, h2⟩ := pushA_fib q s hinj
  by_cases hy : y ∈ (q ∘ s) '' D
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [Function.comp_apply, h1 z hz, finsum_mem_singleton, finsum_mem_singleton, Real.norm_eq_abs]
  · rw [h2 y hy, finsum_mem_empty, finsum_mem_empty, norm_zero]
end ReciprocityTheory.AnForm.M
