-- Prove2me | solution 1 for PI.LocDualGen.EpF.mem_C_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:50:37.458194+00:00
-- url     : https://prove2.me/submissions/bc3d09eb-b223-4983-bcd2-cd282f0b5935

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open ValuativeRel IsDedekindDomain
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
open PI PI.LocDualGen PI.LocDualGen.EpF
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [CharZero K]
local notation "C" => integralClosure 𝒪[K] L
attribute [local instance] dd fr mf tfC
attribute [local instance] sepFR
namespace PI.LocDualGen.EpF
theorem _root_.solution (x : L) : x ∈ (1 : FractionalIdeal (nonZeroDivisors C) L) ↔ x ∈ C := by
  rw [FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
end PI.LocDualGen.EpF
