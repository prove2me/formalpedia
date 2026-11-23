-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.dI_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:08.419739+00:00
-- url     : https://prove2.me/submissions/cbc4592f-899c-4475-8c2c-7a85dc5ffdff

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntA
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_mset

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
theorem _root_.solution {Z : Type} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (φ : OpenPartialHomeomorph Z (Fin e → ℂ)) {E : Set Z} (hE : MeasurableSet E) (g : Z → ℝ)
    (w : (Fin e → ℂ) → ℝ) (hint : IntegrableOn (fun z => g (φ.symm z) * w z) φ.target) :
    IntegrableOn (fun z => E.indicator g (φ.symm z) * w z) φ.target := by
  have h1 := hint.indicator (dI_mset φ hE)
  refine h1.congr_fun (fun z hz => ?_) φ.open_target.measurableSet
  by_cases h : φ.symm z ∈ E
  · rw [Set.indicator_of_mem (show z ∈ φ.target ∩ φ.symm ⁻¹' E from ⟨hz, h⟩),
      Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (show z ∉ φ.target ∩ φ.symm ⁻¹' E from fun h' => h h'.2),
      Set.indicator_of_notMem h, zero_mul]
end ReciprocityTheory.AnForm.M
