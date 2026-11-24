-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_pow_mul_sub_eval__mem_a87e3b5542f1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:56.318188+00:00
-- url     : https://prove2.me/submissions/d0f7d904-763e-47bc-8d2a-b5f752f39cb3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreTor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFibreRadicalPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {σ ι : Type*} {d : ℕ} (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ)))
    (y : Fin d → MvPolynomial ι (MvPolynomial σ ℂ)) (θ : MvPolynomial ι (MvPolynomial σ ℂ))
    (D : MvPolynomial (Fin d) (MvPolynomial σ ℂ)) (q : ι → Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)))
    (hq : ∀ i, aeval y D * X i - Polynomial.eval₂ (aeval y).toRingHom θ (q i) ∈ K)
    (p : MvPolynomial ι (MvPolynomial σ ℂ)) :
    ∃ (e : ℕ) (H : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))),
      aeval y D ^ e * p - Polynomial.eval₂ (aeval y).toRingHom θ H ∈ K := by
  induction p using MvPolynomial.induction_on with
  | C s =>
    refine ⟨0, Polynomial.C (C s), ?_⟩
    simp [MvPolynomial.algebraMap_eq]
  | add p₁ p₂ h₁ h₂ =>
    obtain ⟨e₁, H₁, h₁⟩ := h₁
    obtain ⟨e₂, H₂, h₂⟩ := h₂
    refine ⟨e₁ + e₂, Polynomial.C (D ^ e₂) * H₁ + Polynomial.C (D ^ e₁) * H₂, ?_⟩
    have e : aeval y D ^ (e₁ + e₂) * (p₁ + p₂) -
        Polynomial.eval₂ (aeval y).toRingHom θ (Polynomial.C (D ^ e₂) * H₁ + Polynomial.C (D ^ e₁) * H₂) =
        aeval y D ^ e₂ * (aeval y D ^ e₁ * p₁ - Polynomial.eval₂ (aeval y).toRingHom θ H₁) +
          aeval y D ^ e₁ * (aeval y D ^ e₂ * p₂ - Polynomial.eval₂ (aeval y).toRingHom θ H₂) := by
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, map_pow,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      ring
    rw [e]
    exact K.add_mem (K.mul_mem_left _ h₁) (K.mul_mem_left _ h₂)
  | mul_X p i h =>
    obtain ⟨e, H, h⟩ := h
    refine ⟨e + 1, H * q i, ?_⟩
    have e' : aeval y D ^ (e + 1) * (p * X i) - Polynomial.eval₂ (aeval y).toRingHom θ (H * q i) =
        (aeval y D ^ e * p - Polynomial.eval₂ (aeval y).toRingHom θ H) * (aeval y D * X i) +
          Polynomial.eval₂ (aeval y).toRingHom θ H *
            (aeval y D * X i - Polynomial.eval₂ (aeval y).toRingHom θ (q i)) := by
      rw [Polynomial.eval₂_mul]
      ring
    rw [e']
    exact K.add_mem (K.mul_mem_right _ h) (K.mul_mem_left _ (hq i))
end GroundTheory.Heights₂.Heights
