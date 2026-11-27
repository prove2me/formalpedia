-- Prove2me | solution 1 for P2M_GlobalTheory_localized__saturation_fractionRing_55c6950ea93b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:52:56.707536+00:00
-- url     : https://prove2.me/submissions/db3954b8-da07-4fc1-bf20-dd51683f33d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_isSaturatedSubmodule_of_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  (f : M →ₗ[R] V) [IsLocalizedModule R⁰ f]
namespace GlobalTheory
theorem _root_.solution (N : Submodule R M) :
    (saturation N).localized' K R⁰ f = N.localized' K R⁰ f := by
  rw [localized'_saturation K R⁰ f le_rfl, (isSaturatedSubmodule_of_field _).saturation_eq]
end GlobalTheory
