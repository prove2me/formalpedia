-- Prove2me | solution 1 for PI.LocDualGen.FpD.exists_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:58:14.085793+00:00
-- url     : https://prove2.me/submissions/9e12d82f-466e-494c-9b20-ce9844330213

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDual
import Theorems.Thm_PI_LocDualGen_FpD_tr_alg_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open ValuativeRel
namespace PI.LocDualGen.FpD
open PI.LocDualGen.W
section
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
private theorem t2_lemma : T2Space K := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep ?_
  intro x hx
  have hv : ValuativeRel.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  refine ⟨{z | ValuativeRel.valuation K z < ValuativeRel.valuation K x}, ?_, fun h => lt_irrefl (ValuativeRel.valuation K x) h⟩
  exact (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨Units.mk0 _ hv, fun z hz => hz⟩
private theorem trace_cont_lemma_3 (hcont : Continuous (algebraMap ℚ_[l] K)) :
    Continuous (Algebra.trace ℚ_[l] K) := by
  haveI := t2_lemma (K := K)
  haveI : ContinuousSMul ℚ_[l] K := ⟨by
    simp only [Algebra.smul_def]
    exact (hcont.comp continuous_fst).mul continuous_snd⟩
  exact LinearMap.continuous_of_finiteDimensional _
end
end PI.LocDualGen.FpD
end
end

set_option autoImplicit false
noncomputable section
open ValuativeRel
open PI PI.LocDualGen PI.LocDualGen.FpD
open PI.LocDualGen.W
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
namespace PI.LocDualGen.FpD
theorem _root_.solution (hcont : Continuous (algebraMap ℚ_[l] K)) : ∃ x : K, x ≠ 0 ∧ P l x := by
  have hT := trace_cont_lemma_3 l hcont
  have hcpt : IsCompact (𝒪[K] : Set K) := by
    have h : CompactSpace 𝒪[K] := inferInstance
    exact isCompact_iff_compactSpace.2 h
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hT.continuousOn
  have hl1 : ‖(l : ℚ_[l])‖ < 1 := (by first
      | exact Padic.norm_p_lt_one
      | (rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)))
  have hpos : (0 : ℝ) < max C 1 := lt_of_lt_of_le one_pos (le_max_right C 1)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hpos) hl1
  refine ⟨algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ n), ?_, fun b => ?_⟩
  · rw [Ne, map_eq_zero_iff _ (algebraMap ℚ_[l] K).injective]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  · rw [tr_alg_mul, norm_mul, norm_pow]
    have h1 : ‖Algebra.trace ℚ_[l] K (b : K)‖ ≤ max C 1 := (hC b b.2).trans (le_max_left _ _)
    calc ‖(l : ℚ_[l])‖ ^ n * ‖Algebra.trace ℚ_[l] K (b : K)‖
        ≤ ‖(l : ℚ_[l])‖ ^ n * max C 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (max C 1)⁻¹ * max C 1 := mul_le_mul_of_nonneg_right hn.le hpos.le
      _ = 1 := inv_mul_cancel₀ hpos.ne'
end PI.LocDualGen.FpD
