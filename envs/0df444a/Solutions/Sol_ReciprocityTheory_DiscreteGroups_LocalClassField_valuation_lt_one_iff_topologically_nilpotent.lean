-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.valuation_lt_one_iff_topologically_nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:56:51.89955+00:00
-- url     : https://prove2.me/submissions/0e43bb4c-23e3-4a68-b5e7-4bc25367c682

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ValuativeRel Function Filter Topology
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (x : K) :
    valuation K x < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  constructor
  · intro hx
    rw [(IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff]
    intro γ _
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hx γ
    filter_upwards [eventually_ge_atTop n] with m hm
    rw [map_pow]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hx.le hm) hn
  · intro h
    have h1 := (IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff.1 h 1 trivial
    obtain ⟨n, hn⟩ := (h1.and (eventually_ge_atTop 1)).exists
    obtain ⟨hn1, hn2⟩ := hn
    rw [Set.mem_ofPred_eq, map_pow, Units.val_one] at hn1
    by_contra hc
    exact absurd hn1 (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))
end ReciprocityTheory.DiscreteGroups.LocalClassField
