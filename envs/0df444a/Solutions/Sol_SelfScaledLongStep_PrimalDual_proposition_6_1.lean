-- Prove2me | solution 1 for SelfScaledLongStep.PrimalDual.proposition_6_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:19:50.445449+00:00
-- url     : https://prove2.me/submissions/1595a582-f7a5-41eb-bd72-e20f5f392eeb

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_PrimalDual_Defs

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

open SelfScaledLongStep.PrimalDual in
theorem solution {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hA : Function.Surjective A)
    (w : EuclideanSpace ℝ (Fin n)) (hw : w ∈ interior K) (u : EuclideanSpace ℝ (Fin n)) :
    ∃! yp : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n),
      IsProjection F A w u yp.1 yp.2 := by
  have hpos : ∀ h : EuclideanSpace ℝ (Fin n), h ≠ 0 → 0 < ⟪hess F w h, h⟫_ℝ :=
    hF.1.2.2.2.2 w hw
  let Φ : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :=
    LinearMap.prod ((A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ∘ₗ
        LinearMap.snd ℝ _ _)
      (((ContinuousLinearMap.adjoint A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
          EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) ∘ₗ LinearMap.fst ℝ _ _ +
        ((hess F w : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
          EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) ∘ₗ LinearMap.snd ℝ _ _)
  have hΦ : ∀ yp, Φ yp = (A yp.2, ContinuousLinearMap.adjoint A yp.1 + hess F w yp.2) := by
    intro yp; rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨y, p⟩ h
    rw [hΦ] at h
    simp only [Prod.mk_eq_zero] at h
    obtain ⟨h1, h2⟩ := h
    have hp : p = 0 := by
      by_contra hne
      have := hpos p hne
      have e : hess F w p = -(ContinuousLinearMap.adjoint A y) := eq_neg_of_add_eq_zero_right h2
      rw [e, inner_neg_left, ContinuousLinearMap.adjoint_inner_left, h1, inner_zero_right,
        neg_zero] at this
      exact lt_irrefl _ this
    subst hp
    rw [map_zero, add_zero] at h2
    obtain ⟨z, hz⟩ := hA y
    have : ⟪y, y⟫_ℝ = 0 := by
      rw [← hz, ← ContinuousLinearMap.adjoint_inner_left, hz, h2, inner_zero_left]
    have hy : y = 0 := inner_self_eq_zero.mp this
    simp [hy]
  have hsurj : Function.Surjective Φ := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨yp, hyp⟩ := hsurj (0, u)
  refine ⟨yp, ?_, ?_⟩
  · rw [hΦ] at hyp
    simp only [Prod.mk.injEq] at hyp
    exact ⟨hyp.1, hyp.2⟩
  · intro yp' hyp'
    apply hinj
    rw [hΦ, hΦ, hyp'.1, hyp'.2]
    rw [hΦ] at hyp
    exact hyp.symm
