-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_dvd_of_eval__mem_fibre_bf23f9997b48
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:52:05.058484+00:00
-- url     : https://prove2.me/submissions/b24e1e6e-2c7c-4c31-9dd9-64c1e7ae542c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreTor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFibreRadicalPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_fibreMap_eval__aeval_d46a46815112
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_of_mem_ker_fibreMap_c7c611ab7d4e

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
    (m : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))) (D : MvPolynomial (Fin d) (MvPolynomial σ ℂ))
    (q : ι → Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)))
    (hker : ∀ H : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)),
      Polynomial.eval₂ (aeval y).toRingHom θ H ∈ K ↔ m ∣ H)
    (hq : ∀ i, aeval y D * X i - Polynomial.eval₂ (aeval y).toRingHom θ (q i) ∈ K) (t : σ → ℂ)
    (h : Polynomial (MvPolynomial (Fin d) ℂ))
    (hh : Polynomial.eval₂ (aeval fun j => MvPolynomial.map (eval t) (y j)).toRingHom
        (MvPolynomial.map (eval t) θ) h ∈ K.map (MvPolynomial.map (eval t))) :
    ∃ e : ℕ, m.map (MvPolynomial.map (eval t)) ∣
      Polynomial.C (MvPolynomial.map (eval t) D) ^ e * h := by
  have hs : Function.Surjective (eval t : MvPolynomial σ ℂ →+* ℂ) := fun c => ⟨C c, eval_C c⟩
  obtain ⟨H, rfl⟩ := Polynomial.map_surjective _ (MvPolynomial.map_surjective _ hs) h
  rw [← fibreMap_eval₂_aeval] at hh
  obtain ⟨κ, hκ, hκH⟩ := (Ideal.mem_map_iff_of_surjective _ (MvPolynomial.map_surjective _ hs)).1 hh
  have hw : Polynomial.eval₂ (aeval y).toRingHom θ H - κ ∈ RingHom.ker (MvPolynomial.map (eval t) :
      MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) := by
    rw [RingHom.mem_ker, map_sub, hκH, sub_self]
  obtain ⟨e, W, hW, hWK⟩ := exists_of_mem_ker_fibreMap K y θ D q hq t _ hw
  refine ⟨e, ?_⟩
  have hmem : Polynomial.eval₂ (aeval y).toRingHom θ (Polynomial.C D ^ e * H - W) ∈ K := by
    have e' : Polynomial.eval₂ (aeval y).toRingHom θ (Polynomial.C D ^ e * H - W) =
        (aeval y D ^ e * (Polynomial.eval₂ (aeval y).toRingHom θ H - κ) -
          Polynomial.eval₂ (aeval y).toRingHom θ W) + aeval y D ^ e * κ := by
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      ring
    rw [e']
    exact K.add_mem hWK (K.mul_mem_left _ hκ)
  have hd := Polynomial.map_dvd (MvPolynomial.map (eval t)) ((hker _).1 hmem)
  simpa [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, hW] using hd
end GroundTheory.Heights₂.Heights
