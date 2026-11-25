-- Prove2me | solution 1 for PI.EF.Loc.logDeriv_prod_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:37:15.510006+00:00
-- url     : https://prove2.me/submissions/1b7c07ea-31b9-4244-9d12-5debec247175

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
theorem _root_.solution {Z : Finset ℂ} {m : ℂ → ℕ} {φ : ℂ → ℂ → ℂ} {h : ℂ → ℂ} {s : ℂ}
    (hφ : ∀ ρ ∈ Z, φ ρ s ≠ 0) (hφd : ∀ ρ ∈ Z, DifferentiableAt ℂ (φ ρ) s) (hh : h s ≠ 0)
    (hhd : DifferentiableAt ℂ h s) :
    logDeriv (fun z => (∏ ρ ∈ Z, (φ ρ z) ^ (m ρ)) * h z) s =
      (∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (φ ρ) s) + logDeriv h s := by
  have hP : (∏ ρ ∈ Z, (φ ρ s) ^ (m ρ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hφ ρ hρ)
  have hPd : DifferentiableAt ℂ (fun z => ∏ ρ ∈ Z, (φ ρ z) ^ (m ρ)) s :=
    by
      have h5 := DifferentiableAt.finset_prod (f := fun ρ z => (φ ρ z) ^ (m ρ)) (fun ρ hρ => (hφd ρ hρ).pow _)
      rwa [Finset.prod_fn] at h5
  rw [logDeriv_mul (f := fun z => ∏ ρ ∈ Z, (φ ρ z) ^ (m ρ)) (g := h) (x := s) hP hh hPd hhd]
  congr 1
  have h6 := logDeriv_prod (f := fun ρ z => (φ ρ z) ^ (m ρ)) (s := Z) (x := s)
    (fun ρ hρ => pow_ne_zero _ (hφ ρ hρ)) (fun ρ hρ => (hφd ρ hρ).pow _)
  rw [h6]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  exact logDeriv_fun_pow (hφd ρ hρ) (m ρ)
end PI.EF.Loc
