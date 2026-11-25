-- Prove2me | solution 1 for PI.AprimeInfW.exists_local_solve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:22.438255+00:00
-- url     : https://prove2.me/submissions/71148f7a-a707-4f9b-bad5-031337629e8c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ExistsLocalSolve
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.AprimeInfW
open Topology Filter
private theorem local_right_inverse_lemma {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (F : E → E) (f' : E ≃L[ℝ] E) (a : E)
    (hf : HasStrictFDerivAt F (f' : E →L[ℝ] E) a) :
    ∃ φ : E → E, ContinuousAt φ (F a) ∧ φ (F a) = a ∧ ∀ᶠ y in 𝓝 (F a), F (φ y) = y :=
  ⟨hf.localInverse F f' a, hf.localInverse_continuousAt, hf.localInverse_apply_image,
    hf.eventually_right_inverse⟩
end PI.AprimeInfW
end
end

set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfW
open Topology Filter
namespace PI.AprimeInfW
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V] {N : ℕ}
    (e : V ≃ₜ (Fin N → ℝ)) (he : ∀ x y, e (x + y) = e x + e y)
    (B : V → V → V) (hB1 : ∀ x x' y, B (x + x') y = B x y + B x' y)
    (hB2 : ∀ x y y', B x (y + y') = B x y + B x y')
    (hBc : Continuous (fun p : V × V => B p.1 p.2))
    (L : V → V) (hL : ∀ x y, L (x + y) = L x + L y) (hLc : Continuous L)
    (x0 : V) (hD : ∀ u, B x0 u + B u x0 + L u = u + u) :
    ∃ g : V → V, ContinuousAt g (B x0 x0 + L x0) ∧ g (B x0 x0 + L x0) = x0 ∧
      ∀ᶠ y in 𝓝 (B x0 x0 + L x0), B (g y) (g y) + L (g y) = y := by
  have hs : ∀ a b : Fin N → ℝ, e.symm (a + b) = e.symm a + e.symm b := fun a b =>
    e.injective (by rw [he]; simp)
  let b : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) := fun z w => e (B (e.symm z) (e.symm w))
  have hb1 : ∀ z z' w, b (z + z') w = b z w + b z' w := fun z z' w => by
    simp only [b]; rw [hs, hB1, he]
  have hb2 : ∀ z w w', b z (w + w') = b z w + b z w' := fun z w w' => by
    simp only [b]; rw [hs, hB2, he]
  have hpair : Continuous fun p : (Fin N → ℝ) × (Fin N → ℝ) => (e.symm p.1, e.symm p.2) :=
    (e.symm.continuous.comp continuous_fst).prodMk (e.symm.continuous.comp continuous_snd)
  have hbc : Continuous fun p : (Fin N → ℝ) × (Fin N → ℝ) => b p.1 p.2 :=
    e.continuous.comp (hBc.comp hpair)
  have hb3 : ∀ (c : ℝ) z w, b (c • z) w = c • b z w := fun c z w =>
    map_real_smul (AddMonoidHom.mk' (fun z => b z w) fun z z' => hb1 z z' w)
      (hbc.comp (continuous_id.prodMk continuous_const)) c z
  have hb4 : ∀ (c : ℝ) z w, b z (c • w) = c • b z w := fun c z w =>
    map_real_smul (AddMonoidHom.mk' (fun w => b z w) fun w w' => hb2 z w w')
      (hbc.comp (continuous_const.prodMk continuous_id)) c w
  let l : (Fin N → ℝ) → (Fin N → ℝ) := fun z => e (L (e.symm z))
  have hl1 : ∀ z z', l (z + z') = l z + l z' := fun z z' => by
    simp only [l]; rw [hs, hL, he]
  have hlc : Continuous l := e.continuous.comp (hLc.comp e.symm.continuous)
  let lc : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := (AddMonoidHom.mk' l hl1).toRealLinearMap hlc
  let β₂ : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) := LinearMap.mk₂ ℝ b hb1 hb3 hb2 hb4
  let βc : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : ((Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) ≃ₗ[ℝ]
        ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ))).toLinearMap ∘ₗ β₂)
  have hF : ∀ z, e (B (e.symm z) (e.symm z) + L (e.symm z)) = βc z z + lc z := fun z => by
    rw [he]; rfl
  have hD' : ∀ u, βc (e x0) u + βc u (e x0) + lc u = (2 : ℝ) • u := fun u => by
    show e (B (e.symm (e x0)) (e.symm u)) + e (B (e.symm u) (e.symm (e x0))) + e (L (e.symm u))
      = (2 : ℝ) • u
    rw [← he, ← he, e.symm_apply_apply, hD, he, e.apply_symm_apply, two_smul]
  have hder : HasStrictFDerivAt (fun z => βc z z + lc z)
      ((2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ)) (e x0) := by
    have h1 := (βc.hasStrictFDerivAt_of_bilinear (hasStrictFDerivAt_id (e x0))
      (hasStrictFDerivAt_id (e x0))).add lc.hasStrictFDerivAt
    refine h1.congr_fderiv (ContinuousLinearMap.ext fun u => ?_)
    change _ = (2 : ℝ) • u
    rw [← hD' u]
    rfl
  let f' : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ) := ContinuousLinearEquiv.equivOfInverse
    ((2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ))
    ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ))
    (fun u => by simp [smul_smul]) (fun u => by simp [smul_smul])
  have hf : HasStrictFDerivAt (fun z => e (B (e.symm z) (e.symm z) + L (e.symm z)))
      (f' : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) (e x0) := by
    have hfun : (fun z => e (B (e.symm z) (e.symm z) + L (e.symm z))) = fun z => βc z z + lc z :=
      funext hF
    rw [hfun]
    exact hder.congr_fderiv (ContinuousLinearMap.ext fun u => rfl)
  obtain ⟨φ, h1, h2, h3⟩ := local_right_inverse_lemma _ f' (e x0) hf
  simp only [e.symm_apply_apply] at h1 h2 h3
  refine ⟨fun y => e.symm (φ (e y)), ?_, ?_, ?_⟩
  · exact e.symm.continuous.continuousAt.comp (h1.comp e.continuous.continuousAt)
  · simp only [h2, e.symm_apply_apply]
  · exact (e.continuous.continuousAt.tendsto.eventually h3).mono fun y hy => e.injective hy
end PI.AprimeInfW
