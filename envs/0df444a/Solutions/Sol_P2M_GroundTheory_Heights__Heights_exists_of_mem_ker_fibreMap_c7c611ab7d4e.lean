-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_of_mem_ker_fibreMap_c7c611ab7d4e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:42:36.383602+00:00
-- url     : https://prove2.me/submissions/605b504d-b784-4717-a458-93bd52e44a30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreTor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFibreRadicalPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_pow_mul_sub_eval__mem_a87e3b5542f1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ker_fibreMap_fecc3aecf518


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
    (hq : ∀ i, aeval y D * X i - Polynomial.eval₂ (aeval y).toRingHom θ (q i) ∈ K) (t : σ → ℂ)
    (w : MvPolynomial ι (MvPolynomial σ ℂ))
    (hw : w ∈ RingHom.ker (MvPolynomial.map (eval t) :
      MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ)) :
    ∃ (e : ℕ) (W : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))),
      W.map (MvPolynomial.map (eval t)) = 0 ∧
        aeval y D ^ e * w - Polynomial.eval₂ (aeval y).toRingHom θ W ∈ K := by
  set δ : MvPolynomial ι (MvPolynomial σ ℂ) := aeval y D
  set ev : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) → MvPolynomial ι (MvPolynomial σ ℂ) :=
    Polynomial.eval₂ (aeval y).toRingHom θ
  let J : Ideal (MvPolynomial ι (MvPolynomial σ ℂ)) :=
    { carrier := {w | ∃ (e : ℕ) (W : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))),
        W.map (MvPolynomial.map (eval t)) = 0 ∧ δ ^ e * w - ev W ∈ K}
      add_mem' := by
        rintro a b ⟨e₁, W₁, hW₁, h₁⟩ ⟨e₂, W₂, hW₂, h₂⟩
        refine ⟨e₁ + e₂, Polynomial.C (D ^ e₂) * W₁ + Polynomial.C (D ^ e₁) * W₂, ?_, ?_⟩
        · simp [Polynomial.map_add, Polynomial.map_mul, hW₁, hW₂]
        · have e : δ ^ (e₁ + e₂) * (a + b) - ev (Polynomial.C (D ^ e₂) * W₁ + Polynomial.C (D ^ e₁) * W₂) =
              δ ^ e₂ * (δ ^ e₁ * a - ev W₁) + δ ^ e₁ * (δ ^ e₂ * b - ev W₂) := by
            simp only [ev, δ, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
              map_pow, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
            ring
          rw [e]
          exact K.add_mem (K.mul_mem_left _ h₁) (K.mul_mem_left _ h₂)
      zero_mem' := ⟨0, 0, by simp, by simp [ev]⟩
      smul_mem' := by
        rintro r a ⟨e, W, hW, h⟩
        obtain ⟨e', H, hH⟩ := exists_pow_mul_sub_eval₂_mem K y θ D q hq r
        refine ⟨e' + e, H * W, by simp [Polynomial.map_mul, hW], ?_⟩
        have e'' : δ ^ (e' + e) * (r • a) - ev (H * W) =
            δ ^ e * a * (δ ^ e' * r - ev H) + ev H * (δ ^ e * a - ev W) := by
          simp only [ev, Polynomial.eval₂_mul, smul_eq_mul]
          ring
        rw [e'']
        exact K.add_mem (K.mul_mem_left _ hH) (K.mul_mem_left _ h) }
  have hle : RingHom.ker (MvPolynomial.map (eval t) :
      MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) ≤ J := by
    rw [ker_fibreMap, Ideal.map_le_iff_le_comap]
    intro c hc
    refine ⟨0, Polynomial.C (C c), ?_, ?_⟩
    · rw [RingHom.mem_ker] at hc
      simp [hc]
    · simp [ev, MvPolynomial.algebraMap_eq]
  exact hle hw
end GroundTheory.Heights₂.Heights
