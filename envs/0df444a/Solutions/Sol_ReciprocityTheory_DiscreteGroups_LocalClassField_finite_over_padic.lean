-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.finite_over_padic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:59:26.941316+00:00
-- url     : https://prove2.me/submissions/8c392dd9-f4d8-4f8d-ae0a-c79519642c47

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_hausdorff_local_field

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
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (p : ℕ) [Fact p.Prime] (f : ℚ_[p] →+* K) (hf : Continuous f) :
    letI := f.toAlgebra
    FiniteDimensional ℚ_[p] K := by
  let := f.toAlgebra
  have := hausdorff_local_field K
  have : ContinuousSMul ℚ_[p] K := continuousSMul_of_algebraMap _ _ hf
  exact FiniteDimensional.of_locallyCompactSpace ℚ_[p]
end ReciprocityTheory.DiscreteGroups.LocalClassField
