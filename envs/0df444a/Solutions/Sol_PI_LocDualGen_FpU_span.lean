-- Prove2me | solution 1 for PI.LocDualGen.FpU.span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:17:32.573965+00:00
-- url     : https://prove2.me/submissions/76e003d8-b783-4c8f-8a6d-80ad1afab155

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_IsClosedO
import Theorems.Thm_PI_LocDualGen_FpU_Phi_coe
import Theorems.Thm_PI_LocDualGen_FpU_n_step

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
theorem _root_.solution (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (x : 𝒪[K]) : ∃ c, x = Phi K l hcont c := by
  haveI : T2Space K := t2 (K := K)
  choose c y hxy using fun j => n_step K l hcont huni j x
  let F : (Fin (fdim K l) → ℤ_[l]) → K := fun c => ((Phi K l hcont c : 𝒪[K]) : K)
  have hF : Continuous F := by
    have : F = fun c => ∑ i, algebraMap ℚ_[l] K (c i : ℚ_[l]) * (blift K l i : K) := by
      funext c
      exact Phi_coe K l hcont c
    rw [this]
    refine continuous_finset_sum _ (fun i _ => ?_)
    exact (hcont.comp (continuous_subtype_val.comp (continuous_apply i))).mul continuous_const
  have hcl : IsClosed (Set.range F) := (isCompact_range hF).isClosed
  have h0 : Filter.Tendsto (fun j => (l : K) ^ j * (y j : K)) Filter.atTop (nhds 0) := by
    have hp : Filter.Tendsto (fun j => (l : ℚ_[l]) ^ j) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
    have hp' : Filter.Tendsto (fun j => (l : K) ^ j) Filter.atTop (nhds 0) := by
      have := (hcont.tendsto 0).comp hp
      simpa [Function.comp_def, map_pow, map_natCast] using this
    rw [(IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff] at hp' ⊢
    intro γ _
    filter_upwards [hp' γ trivial] with j hj
    have hj' : valuation K ((l : K) ^ j) < γ := hj
    show valuation K ((l : K) ^ j * (y j : K)) < γ
    rw [map_mul]
    have hy1 : valuation K (y j : K) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (y j).2
    calc valuation K ((l : K) ^ j) * valuation K (y j : K) ≤ valuation K ((l : K) ^ j) * 1 :=
          by gcongr
      _ = valuation K ((l : K) ^ j) := mul_one _
      _ < _ := hj'
  have heq : (fun j => F (c j)) = fun j => (x : K) - (l : K) ^ j * (y j : K) := by
    funext j
    have := congrArg (fun z : 𝒪[K] => (z : K)) (hxy j)
    push_cast at this
    simp only [F]
    rw [this]
    ring
  have hlim : Filter.Tendsto (fun j => F (c j)) Filter.atTop (nhds (x : K)) := by
    rw [heq]
    simpa using (tendsto_const_nhds (x := (x : K))).sub h0
  obtain ⟨c0, hc0⟩ := hcl.mem_of_tendsto hlim (Filter.Eventually.of_forall fun j => ⟨c j, rfl⟩)
  exact ⟨c0, Subtype.ext hc0.symm⟩
end PI.LocDualGen.FpU
