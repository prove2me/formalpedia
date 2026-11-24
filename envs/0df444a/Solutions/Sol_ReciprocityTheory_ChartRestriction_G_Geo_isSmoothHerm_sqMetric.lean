-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_sqMetric
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:47.972552+00:00
-- url     : https://prove2.me/submissions/0147a8ac-06d6-42b1-a834-9bc5c749890a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF

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
open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (b : K → ℕ) : IsSmoothHerm (HermLine.sqMetric (ι := ι) b) := by
  unfold IsSmoothHerm
  have hs : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (Σ k, ι k) → ℂ => ∑ i, ‖z ⟨k, i⟩‖ ^ 2) := by
    intro k
    apply ContDiff.sum
    intro i _
    exact (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ (⟨k, i⟩ : Σ k, ι k))
  show ContDiffOn ℝ _ (fun z : (Σ k, ι k) → ℂ => ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ b k) _
  apply contDiffOn_prod
  intro k _
  apply ContDiffOn.pow
  apply ContDiffOn.sqrt (hs k).contDiffOn
  intro z hz
  obtain ⟨i, hi⟩ := hz k
  have hpos : 0 < ‖z ⟨k, i⟩‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi) 2
  exact (lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2)
    (fun i _ => by positivity) (Finset.mem_univ i))).ne'
end ReciprocityTheory.ChartRestriction.G.Geo
