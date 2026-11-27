-- Prove2me | solution 1 for PI.LocDualGen.FpD.bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:15:56.0184+00:00
-- url     : https://prove2.me/submissions/48b15c73-c74d-49b6-ba2e-502c42ac0c9f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDual
import Theorems.Thm_PI_LocDualGen_FpD_norm_l_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel
open PI PI.LocDualGen PI.LocDualGen.FpD
open PI.LocDualGen.W
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
namespace PI.LocDualGen.FpD
theorem _root_.solution : ∃ m : ℕ, ∀ x : K, P l x → algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x ∈ 𝒪[K] := by
  have hn : ((Module.finrank ℚ_[l] K : ℕ) : ℚ_[l]) ≠ 0 := by
    have : 0 < Module.finrank ℚ_[l] K := Module.finrank_pos
    exact_mod_cast this.ne'
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hn) (Padic.norm_p_lt_one (p := l))
  refine ⟨m, fun x hx => ?_⟩
  by_contra hcx
  rw [Valuation.mem_integer_iff, not_le] at hcx
  have hcx0 : algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x ≠ 0 := by
    intro h
    rw [h, map_zero] at hcx
    exact absurd hcx (not_lt.mpr zero_le)
  have hb : (algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x)⁻¹ ∈ 𝒪[K] := by
    rw [Valuation.mem_integer_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ hcx.le
  have hx0 : x ≠ 0 := right_ne_zero_of_mul hcx0
  have hc0 : algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) ≠ 0 := left_ne_zero_of_mul hcx0
  have h1 := hx ⟨_, hb⟩
  change ‖Algebra.trace ℚ_[l] K (x * (algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x)⁻¹)‖ ≤ 1 at h1
  have e : x * (algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x)⁻¹ =
      algebraMap ℚ_[l] K (((l : ℚ_[l]) ^ m)⁻¹) := by
    rw [map_inv₀]
    field_simp
  rw [e, Algebra.trace_algebraMap, nsmul_eq_mul, norm_mul, norm_inv, norm_pow] at h1
  have hpos : 0 < ‖(l : ℚ_[l])‖ ^ m := pow_pos (norm_l_pos l) m
  rw [mul_inv_le_iff₀ hpos, one_mul] at h1
  exact absurd hm (not_lt.mpr h1)
end PI.LocDualGen.FpD
