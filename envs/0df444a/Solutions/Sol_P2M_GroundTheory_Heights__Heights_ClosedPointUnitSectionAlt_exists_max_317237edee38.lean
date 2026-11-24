-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_max_317237edee38
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:39:53.281813+00:00
-- url     : https://prove2.me/submissions/ca8efa80-0518-4e03-8d17-547dd87568dc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointUnitSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_exists_chart_3dcf866b6f14


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
variable [NumberField K']
namespace GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
theorem _root_.solution (hy : IsArithVar (mCoordIdeal y) 1) (P : HeightOneSpectrum (𝓞 K')) :
    ∃ t : T, y ⟨(), t⟩ ≠ 0 ∧ ∀ u, P.valuation K' (y ⟨(), u⟩) ≤ P.valuation K' (y ⟨(), t⟩) := by
  obtain ⟨t0, ht0⟩ := CurveAffineCharts.exists_chart y hy
  obtain ⟨t, -, ht⟩ := Finset.exists_max_image Finset.univ (fun u => P.valuation K' (y ⟨(), u⟩))
    ⟨t0, Finset.mem_univ _⟩
  refine ⟨t, fun h0 => ht0 ?_, fun u => ht u (Finset.mem_univ _)⟩
  have h1 := ht t0 (Finset.mem_univ _)
  rw [h0, map_zero] at h1
  exact (Valuation.zero_iff _).mp (le_antisymm h1 zero_le)
end GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
