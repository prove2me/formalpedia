-- Prove2me | solution 1 for PI.LocDualGen.EpS.selfDual_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:03:34.148329+00:00
-- url     : https://prove2.me/submissions/7febeda9-54cd-4b14-afbc-61580b3c36a4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualSplit
import Theorems.Thm_PI_LocDualGen_EpS_isIntegral_idem
import Theorems.Thm_PI_LocDualGen_EpS_pr_e
import Theorems.Thm_PI_LocDualGen_EpS_pr_f
import Theorems.Thm_PI_LocDualGen_EpS_trace_eq
import Theorems.Thm_PI_LocDualGen_EpS_int_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Module
open PI PI.LocDualGen PI.LocDualGen.EpS
variable {K : Type} [Field K] {L : Type} [CommRing L] [Algebra K L]
variable (hr : finrank K L = 2) (e : L) (he : IsIdempotentElem e) (h0 : e ≠ 0) (h1 : e ≠ 1)
variable [ValuativeRel K]
include hr he h0 h1
namespace PI.LocDualGen.EpS
theorem _root_.solution (x : L) :
    (∀ y : L, IsIntegral 𝒪[K] y → Algebra.trace K L (x * y) ∈ 𝒪[K]) ↔ IsIntegral 𝒪[K] x := by
  have pe := pr_e hr e he h0 h1
  have pf := pr_f hr e he h0 h1
  constructor
  · intro h
    have ha := h e (isIntegral_idem e he)
    have hb := h (1 - e) (isIntegral_one.sub (isIntegral_idem e he))
    rw [trace_eq hr e he h0 h1, map_mul, map_mul, pe.1, pe.2] at ha
    rw [trace_eq hr e he h0 h1, map_mul, map_mul, pf.1, pf.2] at hb
    simp only [mul_one, mul_zero, add_zero, zero_add] at ha hb
    exact (int_iff hr e he h0 h1 x).mpr ⟨ha, hb⟩
  · intro hx y hy
    have := (int_iff hr e he h0 h1 (x * y)).mp (hx.mul hy)
    rw [trace_eq hr e he h0 h1]
    exact add_mem this.1 this.2
end PI.LocDualGen.EpS
