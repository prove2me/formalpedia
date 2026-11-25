-- Prove2me | solution 1 for PI.LocDualGen.EpF.selfDual_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:57:59.223844+00:00
-- url     : https://prove2.me/submissions/d2312e3a-5182-4a40-bdf2-e3bb4b44ff79

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualField
import Theorems.Thm_PI_LocDualGen_EpF_differentIdeal_eq_top
import Theorems.Thm_PI_LocDualGen_EpF_mem_C_iff

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
theorem _root_.solution
    (hU : ∀ x : C, x * x ∈ Ideal.map (algebraMap 𝒪[K] C) 𝓂[K] →
      x ∈ Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) (x : L) :
    (∀ y ∈ C, Algebra.trace K L (x * y) ∈ 𝒪[K]) ↔ x ∈ C := by
  have hdual : FractionalIdeal.dual 𝒪[K] K (1 : FractionalIdeal (nonZeroDivisors C) L) = 1 := by
    have h := coeIdeal_differentIdeal 𝒪[K] K L C
    rw [differentIdeal_eq_top K L hU, FractionalIdeal.coeIdeal_top] at h
    exact inv_eq_one.1 h.symm
  have hr : ∀ z : K, z ∈ (algebraMap 𝒪[K] K).range ↔ z ∈ 𝒪[K] :=
    fun z => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
  have h10 : (1 : FractionalIdeal (nonZeroDivisors C) L) ≠ 0 := by
    rw [Ne, ← FractionalIdeal.coeIdeal_top, FractionalIdeal.coeIdeal_eq_zero]
    exact top_ne_bot
  rw [← mem_C_iff K L x, ← hdual, FractionalIdeal.mem_dual h10]
  simp only [Algebra.traceForm_apply, mem_C_iff K L, hr]
end PI.LocDualGen.EpF
