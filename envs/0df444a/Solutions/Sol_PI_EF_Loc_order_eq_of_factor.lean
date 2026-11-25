-- Prove2me | solution 1 for PI.EF.Loc.order_eq_of_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:36:27.135669+00:00
-- url     : https://prove2.me/submissions/9cbb5737-3e53-4ada-a1bf-70e6b777b9ed

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormLogDerivReflLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Loc
open Complex Metric Set Filter Topology ComplexConjugate
namespace PI.EF.Loc
theorem _root_.solution {f h : ℂ → ℂ} {Z : Finset ℂ} {m : ℂ → ℕ} {ρ : ℂ} (hρ : ρ ∈ Z) {U : Set ℂ}
    (hU : U ∈ 𝓝 ρ) (hf : AnalyticAt ℂ f ρ) (hh : DifferentiableOn ℂ h U) (hhρ : h ρ ≠ 0)
    (hfac : ∀ z ∈ U, f z = (∏ ρ' ∈ Z, (z - ρ') ^ (m ρ')) * h z) :
    analyticOrderNatAt f ρ = m ρ := by
  have hha : AnalyticAt ℂ h ρ := hh.analyticAt hU
  have hg : AnalyticAt ℂ (fun z => (∏ ρ' ∈ Z.erase ρ, (z - ρ') ^ (m ρ')) * h z) ρ :=
    by
      have h7 := Finset.analyticAt_prod (𝕜 := ℂ) (Z.erase ρ) (f := fun ρ' z => (z - ρ') ^ (m ρ')) (c := ρ)
        (fun ρ' _ => by fun_prop)
      rw [Finset.prod_fn] at h7
      exact h7.mul hha
  have hg0 : (∏ ρ' ∈ Z.erase ρ, (ρ - ρ') ^ (m ρ')) * h ρ ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ρ' hρ' =>
      pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hρ').symm)) hhρ
  have hord : analyticOrderAt f ρ = (m ρ : ℕ∞) := by
    rw [hf.analyticOrderAt_eq_natCast]
    refine ⟨_, hg, hg0, ?_⟩
    filter_upwards [hU] with z hz
    rw [hfac z hz, ← Finset.mul_prod_erase Z (fun ρ' => (z - ρ') ^ (m ρ')) hρ, smul_eq_mul, mul_assoc]
  simp [analyticOrderNatAt, hord]
end PI.EF.Loc
