-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.firstMinimum_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:20.305609+00:00
-- url     : https://prove2.me/submissions/c81bc63c-e956-4caa-83fe-e42f414f9560

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RSubMean
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex Metric
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (Y : GT ι) (hN : 0 < Fintype.card ι) : 0 < Y.la1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_discrete ({0} : Set (lat Y.b))) 0 rfl
  have hne : ({t : ℝ | ∃ x ∈ lat Y.b, x ≠ 0 ∧ t = ‖x‖}).Nonempty := by
    obtain ⟨i⟩ : Nonempty (Fin (2 * Fintype.card ι)) := ⟨⟨0, by omega⟩⟩
    exact ⟨_, Y.b i, Submodule.subset_span ⟨i, rfl⟩, Y.b.ne_zero i, rfl⟩
  unfold GT.la1
  refine lt_of_lt_of_le hε (le_csInf hne ?_)
  rintro t ⟨x, hx, hx0, rfl⟩
  by_contra hlt
  push_neg at hlt
  have hmem : (⟨x, hx⟩ : lat Y.b) ∈ Metric.ball (0 : lat Y.b) ε := by
    simpa [Metric.mem_ball, dist_zero_right] using hlt
  have h0 := hball hmem
  simp only [Set.mem_singleton_iff] at h0
  exact hx0 (congrArg Subtype.val h0)
end ReciprocityTheory.ChartRestriction.G.I2
