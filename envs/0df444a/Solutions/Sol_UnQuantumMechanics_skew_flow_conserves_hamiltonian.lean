-- Prove2me | solution 1 for UnQuantumMechanics.skew_flow_conserves_hamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T02:35:31.271749+00:00
-- url     : https://prove2.me/submissions/df429eed-3337-4894-9eea-488feb227e8c

import Mathlib
import Definitions.Def_UnQM_phase_space

set_option autoImplicit false

open Matrix

theorem d83a3ea5_clm_expand {ν : ℕ} (L : (Fin ν → ℝ) →L[ℝ] ℝ) (v : Fin ν → ℝ) :
    L v = v ⬝ᵥ (fun k => L (Pi.single k 1)) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  simp only [dotProduct]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have : (Pi.single k (v k) : Fin ν → ℝ) = v k • Pi.single k 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, map_smul, smul_eq_mul]

theorem d83a3ea5_skew_quad {ν : ℕ} (J : Matrix (Fin ν) (Fin ν) ℝ) (hJ : Jᵀ = -J)
    (g : Fin ν → ℝ) : (J *ᵥ g) ⬝ᵥ g = 0 := by
  have h1 : g ⬝ᵥ (J *ᵥ g) = (Jᵀ *ᵥ g) ⬝ᵥ g := by
    rw [dotProduct_mulVec, mulVec_transpose]
  rw [hJ, neg_mulVec, neg_dotProduct, dotProduct_comm g] at h1
  linarith

open Matrix in
theorem solution {ν : ℕ} (J : Matrix (Fin ν) (Fin ν) ℝ) (hJ : Jᵀ = -J)
    (Hf : (Fin ν → ℝ) → ℝ) (hHf : Differentiable ℝ Hf) (ψ : ℝ → Fin ν → ℝ)
    (hψ : ∀ τ, HasDerivAt ψ (J *ᵥ (fun k => fderiv ℝ Hf (ψ τ) (Pi.single k 1))) τ) :
    ∀ τ, HasDerivAt (fun t => Hf (ψ t)) 0 τ := by
  intro τ
  have h := (hHf (ψ τ)).hasFDerivAt.comp_hasDerivAt τ (hψ τ)
  rw [d83a3ea5_clm_expand, d83a3ea5_skew_quad J hJ] at h
  exact h
