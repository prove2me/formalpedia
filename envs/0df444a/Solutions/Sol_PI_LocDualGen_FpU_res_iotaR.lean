-- Prove2me | solution 1 for PI.LocDualGen.FpU.res_iotaR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:51:51.73154+00:00
-- url     : https://prove2.me/submissions/3b3cc339-e544-446c-9536-7a5c6044b19c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_IsClosedO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsLocalRing
open PI PI.LocDualGen PI.LocDualGen.FpU
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K]
variable [CharP 𝓀[K] l]
attribute [local instance] algRes
namespace PI.LocDualGen.FpU
theorem _root_.solution (hcont : Continuous (algebraMap ℚ_[l] K)) (a : ℤ_[l]) :
    residue 𝒪[K] (iotaR K l hcont a) = algebraMap (ZMod l) 𝓀[K] (PadicInt.toZMod a) := by
  obtain ⟨-, h⟩ := PadicInt.zmodRepr_spec a
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨b, hb⟩ := h
  have ha : a = ((a.zmodRepr : ℕ) : ℤ_[l]) + b * (l : ℤ_[l]) := by rw [hb]; ring
  rw [ha]
  simp [map_natCast, CharP.cast_eq_zero]
end PI.LocDualGen.FpU
