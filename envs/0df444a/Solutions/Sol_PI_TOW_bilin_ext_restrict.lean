-- Prove2me | solution 1 for PI.TOW.bilin_ext_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:32.367524+00:00
-- url     : https://prove2.me/submissions/a1ce2c23-3ad9-45be-ae8b-be948e3f10d8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.TOW
open PI.TO
namespace PI.TOW
theorem _root_.solution {K : Type} [CommRing K] {σ : Type*} (T : Set (σ →₀ ℕ))
    (Φ Ψ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K →ₗ[K] K)
    (h : ∀ μ ∈ T, ∀ ν ∈ T, Φ (monomial μ 1) (monomial ν 1) = Ψ (monomial μ 1) (monomial ν 1)) :
    ∀ G ∈ restrictSupport K T, ∀ H ∈ restrictSupport K T, Φ G H = Ψ G H := by
  have e : ∀ (ρ : σ →₀ ℕ) (c : K), (monomial ρ c : MvPolynomial σ K) = c • monomial ρ 1 := fun ρ c => by
    rw [smul_monomial, smul_eq_mul, mul_one]
  intro G hG H hH
  rw [MvPolynomial.mem_restrictSupport_iff] at hG hH
  rw [G.as_sum, H.as_sum]
  simp only [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun μ hμ => Finset.sum_congr rfl fun ν hν => ?_
  rw [e μ, e ν]
  simp only [map_smul, LinearMap.smul_apply]
  rw [h ν (hG hν) μ (hH hμ)]
end PI.TOW
