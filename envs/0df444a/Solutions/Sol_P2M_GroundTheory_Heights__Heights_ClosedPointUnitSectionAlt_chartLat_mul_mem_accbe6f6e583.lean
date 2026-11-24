-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_chartLat_mul_mem_accbe6f6e583
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:43.214202+00:00
-- url     : https://prove2.me/submissions/78df8b29-3e0c-49b3-a79b-c2cc4fca0fa4

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
theorem _root_.solution {a b : ℕ} {g h : K'} (hg : g ∈ chartLat y 1 a) (hh : h ∈ chartLat y 1 b) :
    g * h ∈ chartLat y 1 (a + b) := by
  rw [mem_chartLat_iff] at hg hh ⊢
  intro t ht
  rw [pow_add, mul_div_mul_comm]
  exact Subalgebra.mul_mem _ (hg t ht) (hh t ht)
end GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
