-- Prove2me | solution 1 for SelfScaledLongStep.PathFollow.proposition_6_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T02:25:50.459134+00:00
-- url     : https://prove2.me/submissions/ebd0fe66-38db-437b-bae1-0fde1602ad28

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_PathFollow_Defs

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace Aux_SSLS_63

open InnerProductSpace

lemma hess_symm {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (w : EuclideanSpace ℝ (Fin n))
    (hcd : ContDiffAt ℝ 3 F w) (a b : EuclideanSpace ℝ (Fin n)) :
    ⟪hess F w a, b⟫_ℝ = ⟪a, hess F w b⟫_ℝ := by
  have hsymm := hcd.isSymmSndFDerivAt (by simp; norm_num)
  have hdd : DifferentiableAt ℝ (fderiv ℝ F) w :=
    (hcd.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have hg : gradient F = fun x => (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ F x) := by
    funext x; rfl
  have hH : ∀ v, hess F w v =
      (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ (fderiv ℝ F) w v) := by
    intro v
    unfold hess
    rw [hg]
    have := ((toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearEquiv.hasFDerivAt.comp w
      hdd.hasFDerivAt).fderiv
    rw [show (fun x => (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ F x)) =
      ((toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearEquiv) ∘ fderiv ℝ F from rfl,
      this]
    rfl
  rw [hH, toDual_symm_apply, real_inner_comm, hH, toDual_symm_apply]
  exact hsymm a b

end Aux_SSLS_63

open SelfScaledLongStep.PathFollow Aux_SSLS_63 in
theorem solution {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    {m : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hA : Function.Surjective A)
    (w u : EuclideanSpace ℝ (Fin n)) (hw : w ∈ interior K)
    (y : EuclideanSpace ℝ (Fin m)) (p : EuclideanSpace ℝ (Fin n))
    (hp : SelfScaledLongStep.PrimalDual.IsProjection F A w u y p) :
    (∀ y' : EuclideanSpace ℝ (Fin m),
        lnorm F w p ≤ dnorm F w (u - ContinuousLinearMap.adjoint A y')) ∧
      (∀ y' : EuclideanSpace ℝ (Fin m),
        lnorm F w p = dnorm F w (u - ContinuousLinearMap.adjoint A y') →
          ∀ y'' : EuclideanSpace ℝ (Fin m),
            dnorm F w (u - ContinuousLinearMap.adjoint A y') ≤
              dnorm F w (u - ContinuousLinearMap.adjoint A y'')) := by
  have hpos : ∀ h : EuclideanSpace ℝ (Fin n), h ≠ 0 → 0 < ⟪hess F w h, h⟫_ℝ :=
    hF.1.2.2.2.2 w hw
  have hnn : ∀ h : EuclideanSpace ℝ (Fin n), 0 ≤ ⟪hess F w h, h⟫_ℝ := by
    intro h
    by_cases h0 : h = 0
    · rw [h0, inner_zero_right]
    · exact (hpos h h0).le
  have hcd : ContDiffAt ℝ 3 F w := hF.1.1.2.1.contDiffAt (isOpen_interior.mem_nhds hw)
  have hsym := hess_symm F w hcd
  set H := hess F w with hHd
  have hinj : Function.Injective H := by
    intro a b hab
    by_contra hne
    have h1 := hpos (a - b) (sub_ne_zero.mpr hne)
    have : H (a - b) = 0 := by rw [map_sub]; rw [sub_eq_zero]; exact hab
    rw [this, inner_zero_left] at h1
    exact lt_irrefl _ h1
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (LinearEquiv.ofInjectiveEndo (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
      hinj).toContinuousLinearEquiv
  have he : (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = H := by
    ext v; rfl
  have hinv : H.inverse = (e.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
    rw [← he, ContinuousLinearMap.inverse_equiv]
  have hHinv : ∀ v, H (H.inverse v) = v := by
    intro v
    rw [hinv]
    change H (e.symm v) = v
    have : H (e.symm v) = e (e.symm v) := by rw [← he]; rfl
    rw [this, e.apply_symm_apply]
  have hinvH : ∀ v, H.inverse (H v) = v := by
    intro v
    rw [hinv]
    change e.symm (H v) = v
    have : H v = e v := by rw [← he]; rfl
    rw [this]
    exact e.symm_apply_apply v
  obtain ⟨hAp, hu⟩ := hp
  have part1 : ∀ y' : EuclideanSpace ℝ (Fin m),
      lnorm F w p ≤ dnorm F w (u - ContinuousLinearMap.adjoint A y') := by
    intro y'
    unfold lnorm dnorm
    rw [← hHd]
    apply Real.sqrt_le_sqrt
    set z := y - y' with hz
    have hv : u - ContinuousLinearMap.adjoint A y' = H p + ContinuousLinearMap.adjoint A z := by
      rw [← hu, hz, map_sub]; abel
    set r := H.inverse (ContinuousLinearMap.adjoint A z) with hr
    have hHr : H r = ContinuousLinearMap.adjoint A z := hHinv _
    rw [hv, map_add, hinvH, ← hr]
    have c1 : ⟪p, ContinuousLinearMap.adjoint A z⟫_ℝ = 0 := by
      rw [ContinuousLinearMap.adjoint_inner_right, hAp, inner_zero_left]
    have c2 : ⟪r, H p⟫_ℝ = 0 := by
      rw [← hsym, hHr, ContinuousLinearMap.adjoint_inner_left, hAp, inner_zero_right]
    have c3 : 0 ≤ ⟪r, ContinuousLinearMap.adjoint A z⟫_ℝ := by
      rw [← hHr, real_inner_comm]; exact hnn r
    rw [inner_add_left, inner_add_right, inner_add_right, c1, c2, real_inner_comm p (H p)]
    linarith
  refine ⟨part1, fun y' hy' y'' => ?_⟩
  rw [← hy']
  exact part1 y''
