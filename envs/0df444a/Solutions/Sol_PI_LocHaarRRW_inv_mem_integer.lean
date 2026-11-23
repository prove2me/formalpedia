-- Prove2me | solution 1 for PI.LocHaarRRW.inv_mem_integer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:39.91022+00:00
-- url     : https://prove2.me/submissions/b9fbbf37-f2cd-47ae-835f-0a040cab18e6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_ExistsHaarOfSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel MeasureTheory Topology Polynomial
open PI PI.LocHaarRRW
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
namespace PI.LocHaarRRW
theorem _root_.solution {x : K} (hx : x ∉ 𝒪[K]) : x⁻¹ ∈ 𝒪[K] := by
  rw [Valuation.mem_integer_iff] at hx ⊢
  rw [map_inv₀]
  push Not at hx
  exact inv_le_one_of_one_le₀ hx.le
end PI.LocHaarRRW
