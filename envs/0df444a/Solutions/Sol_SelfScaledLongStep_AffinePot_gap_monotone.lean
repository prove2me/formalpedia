-- Prove2me | solution 1 for SelfScaledLongStep.AffinePot.gap_monotone
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T13:08:39.032597+00:00
-- url     : https://prove2.me/submissions/fc9c08a8-38ba-4dd4-b0fb-a69306742a50

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_AffinePot_Defs

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep
open SelfScaledLongStep.AffinePot
open Filter Topology
open scoped Pointwise

namespace AffPotGapAux

variable {n : ℕ}

lemma inner_gradient (F : EuclideanSpace ℝ (Fin n) → ℝ) (y v : EuclideanSpace ℝ (Fin n)) :
    ⟪gradient F y, v⟫_ℝ = fderiv ℝ F y v := by
  unfold gradient
  rw [InnerProductSpace.toDual_symm_apply]

lemma smul_mem_interior (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (τ : ℝ) (hτ : 0 < τ) :
    τ • x ∈ interior K := by
  have hsub : τ • interior K ⊆ interior K :=
    interior_maximal (by rintro _ ⟨y, hy, rfl⟩; exact hK.2.2.1 y (interior_subset hy) τ hτ.le)
      (isOpen_interior.smul₀ hτ.ne')
  exact hsub (Set.smul_mem_smul_set hx)

lemma diffAt (K : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ)
    (hF : IsSelfScaledBarrier K F ν) (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ interior K) :
    ContDiffAt ℝ 3 F y :=
  hF.1.1.2.1.contDiffAt (isOpen_interior.mem_nhds hy)

lemma hasFDerivAt_F (K : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (ν : ℝ) (hF : IsSelfScaledBarrier K F ν) (y : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ interior K) : HasFDerivAt F (fderiv ℝ F y) y :=
  ((diffAt K F ν hF y hy).differentiableAt (by norm_num)).hasFDerivAt

lemma hasFDerivAt_grad (K : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (ν : ℝ) (hF : IsSelfScaledBarrier K F ν) (y : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ interior K) : HasFDerivAt (gradient F) (hess F y) y := by
  have h1 : ContDiffAt ℝ 2 (fderiv ℝ F) y := (diffAt K F ν hF y hy).fderiv_right (by norm_num)
  have h2 : DifferentiableAt ℝ (fderiv ℝ F) y := h1.differentiableAt (by norm_num)
  have h3 : DifferentiableAt ℝ (gradient F) y := by
    have e : gradient F = fun z => (InnerProductSpace.toDual ℝ _).symm (fderiv ℝ F z) := rfl
    rw [e]
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearEquiv.differentiableAt.comp
      y h2
  exact h3.hasFDerivAt

/-- `⟨F'(y), y⟩ = −ν` on `int K` (differentiate (2.6) in `τ` at `τ = 1`). -/
lemma inner_grad_self (K : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (ν : ℝ) (hF : IsSelfScaledBarrier K F ν) (y : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ interior K) : ⟪gradient F y, y⟫_ℝ = -ν := by
  have hhom := hF.1.2.2.2.1 y hy
  have hL : HasDerivAt (fun τ : ℝ => F (τ • y)) (fderiv ℝ F y ((1 : ℝ) • y)) 1 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (1 : ℝ) (hasFDerivAt_F K F ν hF y hy)
      ((hasDerivAt_id (1 : ℝ)).smul_const y) (by simp)
  have hR : HasDerivAt (fun τ : ℝ => F y - ν * Real.log τ) (-(ν * (1 : ℝ)⁻¹)) 1 :=
    ((Real.hasDerivAt_log one_ne_zero).const_mul ν).const_sub (F y)
  have hev : (fun τ : ℝ => F (τ • y)) =ᶠ[𝓝 1] (fun τ : ℝ => F y - ν * Real.log τ) :=
    (lt_mem_nhds one_pos).mono fun τ hτ => hhom τ hτ
  have := (hL.congr_of_eventuallyEq hev.symm).unique hR
  rw [inner_gradient, ← one_smul ℝ y]
  rw [one_smul] at this ⊢
  simpa using this

/-- `F'(τx) = τ⁻¹ F'(x)`. -/
lemma grad_smul (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hF : IsSelfScaledBarrier K F ν)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (τ : ℝ) (hτ : 0 < τ) :
    gradient F (τ • x) = τ⁻¹ • gradient F x := by
  have hτx := smul_mem_interior K hK x hx τ hτ
  have hL : HasFDerivAt (fun y => F (τ • y))
      ((fderiv ℝ F (τ • x)).comp (τ • ContinuousLinearMap.id ℝ _)) x :=
    (hasFDerivAt_F K F ν hF _ hτx).comp x ((hasFDerivAt_id x).const_smul τ)
  have hR : HasFDerivAt (fun y => F y - ν * Real.log τ) (fderiv ℝ F x) x :=
    (hasFDerivAt_F K F ν hF x hx).sub_const _
  have hev : (fun y => F (τ • y)) =ᶠ[𝓝 x] (fun y => F y - ν * Real.log τ) :=
    Filter.eventually_of_mem (isOpen_interior.mem_nhds hx) fun y hy => hF.1.2.2.2.1 y hy τ hτ
  have heq := (hL.congr_of_eventuallyEq hev.symm).unique hR
  apply ext_inner_right ℝ
  intro v
  rw [real_inner_smul_left, inner_gradient, inner_gradient, ← heq]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  field_simp

/-- `F''(x)x = −F'(x)`. -/
lemma hess_self (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hF : IsSelfScaledBarrier K F ν)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) :
    hess F x x = -gradient F x := by
  have hL : HasDerivAt (fun τ : ℝ => gradient F (τ • x)) (hess F x ((1 : ℝ) • x)) 1 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (1 : ℝ) (hasFDerivAt_grad K F ν hF x hx)
      ((hasDerivAt_id (1 : ℝ)).smul_const x) (by simp)
  have hR : HasDerivAt (fun τ : ℝ => τ⁻¹ • gradient F x) ((-((1 : ℝ) ^ 2)⁻¹) • gradient F x) 1 :=
    (hasDerivAt_inv one_ne_zero).smul_const _
  have hev : (fun τ : ℝ => gradient F (τ • x)) =ᶠ[𝓝 1] (fun τ : ℝ => τ⁻¹ • gradient F x) :=
    (lt_mem_nhds one_pos).mono fun τ hτ => grad_smul K hK F ν hF x hx τ hτ
  have := (hL.congr_of_eventuallyEq hev.symm).unique hR
  simpa using this

/-- `⟨F''(x)p, x⟩ = −⟨F'(x), p⟩` (differentiate `⟨F'(y), y⟩ = −ν`). -/
lemma inner_hess_self (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hF : IsSelfScaledBarrier K F ν)
    (x p : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) :
    ⟪hess F x p, x⟫_ℝ = -⟪gradient F x, p⟫_ℝ := by
  have hline : HasDerivAt (fun t : ℝ => x + t • p) ((1 : ℝ) • p) 0 :=
    ((hasDerivAt_id (0 : ℝ)).smul_const p).const_add x
  have hg : HasDerivAt (fun t : ℝ => gradient F (x + t • p)) (hess F x ((1 : ℝ) • p)) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasFDerivAt_grad K F ν hF x hx) hline (by simp)
  have hφ := hg.inner ℝ hline
  have hc : ContinuousAt (fun t : ℝ => x + t • p) 0 :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have hmem : (fun t : ℝ => x + t • p) ⁻¹' interior K ∈ 𝓝 (0 : ℝ) :=
    hc.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hx)
  have hev : (fun t : ℝ => ⟪gradient F (x + t • p), x + t • p⟫_ℝ) =ᶠ[𝓝 0] (fun _ => -ν) :=
    Filter.mem_of_superset hmem fun t ht => inner_grad_self K F ν hF _ ht
  have h0 := (hφ.congr_of_eventuallyEq hev.symm).unique (hasDerivAt_const (0 : ℝ) (-ν))
  simp only [one_smul, zero_smul, add_zero] at h0
  linarith

end AffPotGapAux

open AffPotGapAux

theorem solution {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hA : Function.Surjective A)
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (hD : ∃ y s, IsDualStrict K A c y s)
    (xh : EuclideanSpace ℝ (Fin n)) (hxh : IsPrimalStrict K A b xh)
    (yc : EuclideanSpace ℝ (Fin m)) (pc : EuclideanSpace ℝ (Fin n))
    (hpc : SelfScaledLongStep.PrimalDual.IsProjection F A xh c yc pc)
    (yd : EuclideanSpace ℝ (Fin m)) (pd : EuclideanSpace ℝ (Fin n))
    (hpd : SelfScaledLongStep.PrimalDual.IsProjection F A xh (gradient F xh) yd pd) :
    (∀ t : ℝ, ⟪sTilde F xh pc pd t, xh⟫_ℝ =
        ⟪-gradient F xh, pc⟫_ℝ + t * ((dnorm F xh (gradient F xh)) ^ 2 - ⟪gradient F xh, pd⟫_ℝ)) ∧
    (∀ t : ℝ, ⟪sTilde F xh pc pd t, xh⟫_ℝ =
        ⟪-gradient F xh, pc⟫_ℝ + t * ((dnorm F xh (gradient F xh)) ^ 2 - (lnorm F xh pd) ^ 2)) ∧
    Monotone (fun t : ℝ => ⟪sTilde F xh pc pd t, xh⟫_ℝ) := by
  have hxi := hxh.1
  have hHx := hess_self K hK F ν hF xh hxi
  have hgx := inner_grad_self K F ν hF xh hxi
  have hposdef := hF.1.2.2.2.2 xh hxi
  have hinj : Function.Injective (hess F xh) := by
    intro u v huv
    by_contra hne
    have h := hposdef (u - v) (sub_ne_zero.2 hne)
    rw [map_sub, huv, sub_self, inner_zero_left] at h
    exact lt_irrefl _ h
  set e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (LinearEquiv.ofInjectiveEndo (hess F xh : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] _) hinj).toContinuousLinearEquiv
    with he
  have heq : (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = hess F xh := by
    ext1 v; rfl
  have hinv : (hess F xh).inverse (gradient F xh) = -xh := by
    rw [← heq, ContinuousLinearMap.inverse_equiv]
    have : gradient F xh = e (-xh) := by
      show gradient F xh = (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (-xh)
      rw [heq, map_neg, hHx, neg_neg]
    rw [this]
    exact ContinuousLinearEquiv.symm_apply_apply e (-xh)
  have hdn : (dnorm F xh (gradient F xh)) ^ 2 = ν := by
    unfold dnorm
    rw [hinv, inner_neg_left, real_inner_comm, hgx, neg_neg]
    exact Real.sq_sqrt (by linarith)
  have hAp := hpd.1
  have hgpd : ⟪gradient F xh, pd⟫_ℝ = ⟪hess F xh pd, pd⟫_ℝ := by
    rw [← hpd.2, inner_add_left, ContinuousLinearMap.adjoint_inner_left, hAp, inner_zero_right,
      zero_add]
  have hLd_nn : 0 ≤ ⟪hess F xh pd, pd⟫_ℝ := by
    by_cases hp : pd = 0
    · rw [hp, map_zero, inner_zero_left]
    · exact (hposdef pd hp).le
  have hln : (lnorm F xh pd) ^ 2 = ⟪gradient F xh, pd⟫_ℝ := by
    unfold lnorm; rw [Real.sq_sqrt hLd_nn, hgpd]
  have hgap : ∀ t : ℝ, ⟪sTilde F xh pc pd t, xh⟫_ℝ =
      ⟪-gradient F xh, pc⟫_ℝ + t * (ν - ⟪gradient F xh, pd⟫_ℝ) := by
    intro t
    unfold sTilde
    rw [map_add, map_smul, inner_sub_left, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, inner_hess_self K F ν hF xh pc hxi,
      inner_hess_self K F ν hF xh pd hxi, hgx, inner_neg_left]
    ring
  have hle : ⟪gradient F xh, pd⟫_ℝ ≤ ν := by
    have h0 : 0 ≤ ⟪hess F xh (pd + xh), pd + xh⟫_ℝ := by
      by_cases hp : pd + xh = 0
      · rw [hp, map_zero, inner_zero_left]
      · exact (hposdef _ hp).le
    have hxx : ⟪hess F xh xh, xh⟫_ℝ = ν := by rw [hHx, inner_neg_left, hgx, neg_neg]
    have hxp : ⟪hess F xh xh, pd⟫_ℝ = -⟪gradient F xh, pd⟫_ℝ := by rw [hHx, inner_neg_left]
    rw [map_add, inner_add_left, inner_add_right, inner_add_right,
      inner_hess_self K F ν hF xh pd hxi, hxx, hxp, ← hgpd] at h0
    linarith
  refine ⟨fun t => by rw [hgap, hdn], fun t => by rw [hgap, hdn, hln], ?_⟩
  intro s t hst
  simp only [hgap]
  have := mul_le_mul_of_nonneg_right hst (by linarith : (0 : ℝ) ≤ ν - ⟪gradient F xh, pd⟫_ℝ)
  linarith
