-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_chartLat_pow_mem_2f024e5dc2e9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:42.563832+00:00
-- url     : https://prove2.me/submissions/95e47ca9-dbc6-44af-bc1e-0cb4d621b387

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointUnitSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_mem_chartLat_iff_f0ffc91e5040
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_chartLat_mul_mem_accbe6f6e583

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
theorem _root_.solution {a : ℕ} {g : K'} (hg : g ∈ chartLat y 1 a) (n : ℕ) :
    g ^ n ∈ chartLat y 1 (a * n) := by
  induction n with
  | zero =>
    rw [mem_chartLat_iff]
    intro t _
    simp
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact chartLat_mul_mem y ih hg
end GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
