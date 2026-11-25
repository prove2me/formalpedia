-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.valuation_intCast_le_one_local_class_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:00:40.233952+00:00
-- url     : https://prove2.me/submissions/e7d80684-32fd-4050-aaf1-2fae1e8bc677

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
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]
  (p : ℕ) [Fact p.Prime]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (n : ℤ) : valuation K (n : K) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 (intCast_mem 𝒪[K] n)
end ReciprocityTheory.DiscreteGroups.LocalClassField
