-- Prove2me | solution 1 for PI.LocHaarRRW.integral_V_of_memO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:58:14.075166+00:00
-- url     : https://prove2.me/submissions/ed1b6f82-aa33-4a49-b1d6-78ca4d292d99

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_ExistsHaarOfSubgroup
import Theorems.Thm_PI_LocHaarRRW_integral_of_memO

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
theorem _root_.solution [Nontrivial V] {y : K} (h : y ∈ 𝒪[K]) :
    IsIntegral 𝒪[K] (algebraMap K V y) :=
  (isIntegral_algebraMap_iff (algebraMap K V).injective).2 (integral_of_memO h)
end PI.LocHaarRRW
