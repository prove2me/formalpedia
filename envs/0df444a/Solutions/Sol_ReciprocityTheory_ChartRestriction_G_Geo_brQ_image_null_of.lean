-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.brQ_image_null_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:04:45.909791+00:00
-- url     : https://prove2.me/submissions/c59e93ff-5872-4612-8d06-552988e7a6fe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_analyticAt_brQ

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
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}
  (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution
    (hS : ∀ j, volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' brBad R Ψ) = 0) :
    volume (brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) = 0 := by
  have hsub : brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0}) ⊆
      ⋃ j, (brQ R Ψ ∘ (R.A.chart j).symm) '' ((R.A.chart j).target ∩
        (R.A.chart j).symm ⁻¹' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hj⟩ := R.A.cover x
    refine Set.mem_iUnion.mpr ⟨j, R.A.chart j x, ⟨(R.A.chart j).map_source hj, ?_⟩, ?_⟩
    · simp only [Set.mem_preimage, (R.A.chart j).left_inv hj]
      exact hx
    · simp [(R.A.chart j).left_inv hj]
  refine measure_mono_null hsub (measure_iUnion_null fun j => ?_)
  apply MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
  · intro v hv
    have hvs : (R.A.chart j).symm v ∈ (R.A.chart j).source := (R.A.chart j).map_target hv.1
    have hA := analyticAt_brQ R Ψ ((R.A.chart j).symm v) j hvs hv.2.2
    rw [(R.A.chart j).right_inv hv.1] at hA
    exact (hA.differentiableAt.restrictScalars ℝ).differentiableWithinAt
  · exact measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left)) (hS j)
end ReciprocityTheory.ChartRestriction.G.Geo
