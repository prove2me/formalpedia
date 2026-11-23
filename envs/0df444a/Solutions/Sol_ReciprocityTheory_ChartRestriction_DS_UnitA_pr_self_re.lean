-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitA.pr_self_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:07:33.090881+00:00
-- url     : https://prove2.me/submissions/b86e3c4c-8424-4890-8e2e-8c4d24dd2724

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_UnitarizeA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_pr_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.UnitA
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] (μ : Measure G)
variable {μ}
namespace ReciprocityTheory.ChartRestriction.DS.UnitA
theorem _root_.solution {a : G → ℂ} (ha : MemLp a 2 μ) :
    pr μ a a = ((∫ x, ‖a x‖ ^ 2 ∂μ : ℝ) : ℂ) ∧ Integrable (fun x => ‖a x‖ ^ 2) μ := by
  have hI : Integrable (fun x => ‖a x‖ ^ 2) μ := by
    refine (pr_int ha ha).norm.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [norm_mul, norm_star, sq]
  refine ⟨?_, hI⟩
  unfold pr
  rw [← integral_complex_ofReal]
  congr 1
  funext x
  rw [Complex.ofReal_pow]
  exact Complex.conj_mul' (a x)
end ReciprocityTheory.ChartRestriction.DS.UnitA
