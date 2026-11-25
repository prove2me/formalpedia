-- Prove2me | solution 1 for PI.LocHaarRRW.integral_of_memO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:51:23.075736+00:00
-- url     : https://prove2.me/submissions/e6ec3bbc-fa3d-4cd7-bcdc-de1f9afe940b

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
variable {K V : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] [CommRing V] [Algebra K V]
namespace PI.LocHaarRRW
theorem _root_.solution {y : K} (h : y ∈ 𝒪[K]) : IsIntegral 𝒪[K] y := by
  have : algebraMap 𝒪[K] K ⟨y, h⟩ = y := rfl
  exact this ▸ isIntegral_algebraMap
end PI.LocHaarRRW
