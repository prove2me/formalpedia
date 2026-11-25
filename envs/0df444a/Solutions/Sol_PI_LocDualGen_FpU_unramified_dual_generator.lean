-- Prove2me | solution 1 for PI.LocDualGen.FpU.unramified_dual_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:18:51.11124+00:00
-- url     : https://prove2.me/submissions/075fbae3-ece6-4849-850c-30d398632aff

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_IsClosedO
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MemOfClosed
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_UnramifiedDualGenerator
import Theorems.Thm_PI_LocDualGen_FpU_trace_int
import Theorems.Thm_PI_LocDualGen_FpU_exists_trace_unit
import Theorems.Thm_PI_LocDualGen_FpU_charP_res


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
namespace PI.LocDualGen.FpU
theorem _root_.solution : PI.LocDualGen.W.FpDualUnram := by
  intro K _ _ _ l _ _ hlf _ hcont _ huni a
  haveI := hlf
  haveI := charP_res K l huni
  letI := algRes K l
  obtain ⟨z, hz⟩ := exists_trace_unit K l hcont huni
  constructor
  · intro H
    by_contra ha
    have ha1 : 1 < valuation K a := by
      rw [Valuation.mem_integer_iff, not_le] at ha
      exact ha
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, map_zero] at ha1
      exact absurd ha1 (not_lt.mpr zero_le)
    have hinv : a⁻¹ ∈ 𝒪[K] := by
      rw [Valuation.mem_integer_iff, map_inv₀]
      exact inv_le_one_of_one_le₀ ha1.le
    have hnu : (⟨a⁻¹, hinv⟩ : 𝒪[K]) ∈ maximalIdeal 𝒪[K] := by
      rw [mem_maximalIdeal, mem_nonunits_iff,
        (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one]
      intro h1
      change valuation K a⁻¹ = 1 at h1
      rw [map_inv₀, inv_eq_one] at h1
      rw [h1] at ha1
      exact lt_irrefl _ ha1
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp huni,
      Ideal.mem_span_singleton'] at hnu
    obtain ⟨t, ht⟩ := hnu
    have ht' : (t : K) * (l : K) = a⁻¹ := congrArg Subtype.val ht
    have hl0 : (l : K) ≠ 0 := by
      rw [← map_natCast (algebraMap ℚ_[l] K)]
      exact (map_ne_zero _).mpr (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
    have hat : a * (t : K) = algebraMap ℚ_[l] K ((l : ℚ_[l])⁻¹) := by
      rw [map_inv₀, map_natCast]
      field_simp
      have := congrArg (fun w => a * w) ht'
      simp only [mul_inv_cancel₀ ha0] at this
      rw [← this]
      ring
    have h1 := H (t * z)
    change ‖Algebra.trace ℚ_[l] K (a * ((t : K) * (z : K)))‖ ≤ 1 at h1
    rw [← mul_assoc, hat, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, norm_mul, norm_inv] at h1
    have hlpos : 0 < ‖(l : ℚ_[l])‖ := norm_pos_iff.mpr (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
    rw [inv_mul_le_iff₀ hlpos, mul_one] at h1
    exact hz (lt_of_le_of_lt h1 Padic.norm_p_lt_one)
  · intro ha b
    exact trace_int K l hcont huni ⟨a * b, mul_mem ha b.2⟩
end PI.LocDualGen.FpU
