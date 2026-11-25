-- Prove2me | solution 1 for PI.AprimeInfW.exists_local_solution_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:18.797123+00:00
-- url     : https://prove2.me/submissions/6baa4a4e-4fa8-4cd2-9cc7-e338c363b801

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ExistsLocalSolutionContDiffAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
      (∀ᶠ y in 𝓝 (B x0 x0 + L x0), B (g y) (g y) + L (g y) = y) ∧
      ContDiffAt ℝ 1 (fun y => e (g (e.symm y))) (e (B x0 x0 + L x0)) ∧
      HasFDerivAt (fun y => e (g (e.symm y))) ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ))
        (e (B x0 x0 + L x0)) := by
  classical
  have hes : ∀ u w, e.symm (u + w) = e.symm u + e.symm w := by
    intro u w
    apply e.injective
    rw [he]
    simp
  let b : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) := fun u w => e (B (e.symm u) (e.symm w))
  let l : (Fin N → ℝ) → (Fin N → ℝ) := fun u => e (L (e.symm u))
  have hb1 : ∀ u u' w, b (u + u') w = b u w + b u' w := by
    intro u u' w
    simp only [b, hes, hB1, he]
  have hb2 : ∀ u w w', b u (w + w') = b u w + b u w' := by
    intro u w w'
    simp only [b, hes, hB2, he]
  have hl1 : ∀ u u', l (u + u') = l u + l u' := by
    intro u u'
    simp only [l, hes, hL, he]
  have hbc : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => b p.1 p.2) :=
    e.continuous.comp (hBc.comp ((e.symm.continuous.comp continuous_fst).prodMk
      (e.symm.continuous.comp continuous_snd)))
  have hlc : Continuous l := e.continuous.comp (hLc.comp e.symm.continuous)
  have hbs1 : ∀ (c : ℝ) u w, b (c • u) w = c • b u w := by
    intro c u w
    exact map_real_smul (AddMonoidHom.mk' (fun u => b u w) (fun u u' => hb1 u u' w))
      (hbc.comp (continuous_id.prodMk continuous_const)) c u
  have hbs2 : ∀ (c : ℝ) u w, b u (c • w) = c • b u w := by
    intro c u w
    exact map_real_smul (AddMonoidHom.mk' (fun w => b u w) (fun w w' => hb2 u w w'))
      (hbc.comp (continuous_const.prodMk continuous_id)) c w
  let b₂ : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) := LinearMap.mk₂ ℝ b hb1 hbs1 hb2 hbs2
  let bL : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : ((Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) ≃ₗ[ℝ]
        ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ))).toLinearMap ∘ₗ b₂)
  let lL : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := (AddMonoidHom.mk' l hl1).toRealLinearMap hlc
  have hbL : ∀ u w, bL u w = b u w := fun u w => rfl
  have hlL : ∀ u, lL u = l u := fun u => rfl
  let Ft : (Fin N → ℝ) → (Fin N → ℝ) := fun u => bL u u + lL u
  have hFt : ∀ u, Ft u = e (B (e.symm u) (e.symm u) + L (e.symm u)) := by
    intro u
    simp only [Ft, hbL, hlL, b, l, he]
  set u0 := e x0 with hu0
  have hy0 : Ft u0 = e (B x0 x0 + L x0) := by rw [hFt, hu0, e.symm_apply_apply]
  have hTwo : ∀ w, bL u0 w + bL w u0 + lL w = (2 : ℝ) • w := by
    intro w
    have h := congrArg e (hD (e.symm w))
    rw [he, he, he, e.apply_symm_apply] at h
    rw [hbL, hbL, hlL, two_smul]
    simpa [b, l, hu0] using h
  let f₁ : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := (2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ)
  let f₂ : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ)
  have h12 : Function.LeftInverse f₂ f₁ := fun w => by
    simp only [f₁, f₂, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_smul]
    norm_num
  have h21 : Function.RightInverse f₂ f₁ := fun w => by
    simp only [f₁, f₂, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_smul]
    norm_num
  let fe : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ) := ContinuousLinearEquiv.equivOfInverse f₁ f₂ h12 h21
  have hFs : HasStrictFDerivAt Ft (fe : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) u0 := by
    have h0 := (bL.hasStrictFDerivAt_of_bilinear (hasStrictFDerivAt_id u0)
      (hasStrictFDerivAt_id u0)).add lL.hasStrictFDerivAt
    refine h0.congr_fderiv ?_
    ext1 w
    show bL u0 w + bL w u0 + lL w = (fe : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) w
    rw [hTwo]
    rfl
  have hcd : ContDiffAt ℝ 1 Ft u0 :=
    ((bL.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id)).add
      lL.contDiff).contDiffAt
  have hs : HasStrictFDerivAt Ft (fe : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) u0 :=
    hcd.hasStrictFDerivAt' hFs.hasFDerivAt one_ne_zero
  let G := hcd.localInverse hFs.hasFDerivAt one_ne_zero
  have hGc : ContinuousAt G (Ft u0) := hs.localInverse_continuousAt
  have hGa : G (Ft u0) = u0 := hs.localInverse_apply_image
  have hGr : ∀ᶠ w in 𝓝 (Ft u0), Ft (G w) = w := hs.eventually_right_inverse
  have hGd : ContDiffAt ℝ 1 G (Ft u0) := hcd.to_localInverse hFs.hasFDerivAt one_ne_zero
  have hGf : HasFDerivAt G ((fe.symm : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))) (Ft u0) :=
    hs.to_localInverse.hasFDerivAt
  rw [hy0] at hGc hGa hGr hGd hGf
  refine ⟨fun y => e.symm (G (e y)), ?_, ?_, ?_, ?_, ?_⟩
  · exact e.symm.continuous.continuousAt.comp (hGc.comp e.continuous.continuousAt)
  · simp only [hGa, hu0, e.symm_apply_apply]
  · have ht : ∀ᶠ y in 𝓝 (B x0 x0 + L x0), Ft (G (e y)) = e y :=
      (e.continuous.tendsto (B x0 x0 + L x0)).eventually hGr
    filter_upwards [ht] with y hy
    rw [hFt] at hy
    exact e.injective (by rw [he]; simpa [he] using hy)
  · have hfun : (fun y => e (e.symm (G (e (e.symm y))))) = G := by
      funext y
      simp
    rw [hfun]
    exact hGd
  · have hfun : (fun y => e (e.symm (G (e (e.symm y))))) = G := by
      funext y
      simp
    rw [hfun]
    convert hGf using 1
    ext1 w
    rfl
end PI.AprimeInfW
