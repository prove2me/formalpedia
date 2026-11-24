-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_coord_mem_e0cbe1c6e1f6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:41.546663+00:00
-- url     : https://prove2.me/submissions/a26b22ac-b080-4af7-b1ed-10d48498d837

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointUnitSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_mem_chartLat_iff_f0ffc91e5040

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
omit [Fintype T]
namespace GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
theorem _root_.solution (u : T) : y ⟨(), u⟩ ∈ chartLat y 1 1 := by
  rw [mem_chartLat_iff]
  intro t _
  rw [pow_one]
  exact Algebra.subset_adjoin ⟨⟨(), u⟩, rfl⟩
end GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
