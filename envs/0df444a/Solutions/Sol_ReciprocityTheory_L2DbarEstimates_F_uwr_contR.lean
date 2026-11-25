-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.uwr_contR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:17:06.787982+00:00
-- url     : https://prove2.me/submissions/6e0e314d-3fd3-4dba-a461-2ca9f88a00c6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightRel
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n}
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (hz : IsLocalHomeomorph z) (f : M → ℝ) (hf : SmoothR n z f) : Continuous f := by
  have hz' := hz
  unfold IsLocalHomeomorph at hz'
  unfold SmoothR Smooth at hf
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, hx, rfl⟩ := hz' x
  have h1 := hf e (fun _ _ => rfl)
  have h2 : ContinuousAt ((fun y => (f y : ℂ)) ∘ e.symm) (e x) :=
    h1.continuousOn.continuousAt (e.open_target.mem_nhds (e.map_source hx))
  have h3 : ContinuousAt (fun y => (f y : ℂ)) x := by
    refine (h2.comp (e.continuousAt hx)).congr ?_
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp [e.left_inv hy]
  have h4 : ContinuousAt (fun y => ((f y : ℂ)).re) x := Complex.continuous_re.continuousAt.comp h3
  simpa using h4
end ReciprocityTheory.L2DbarEstimates.F
