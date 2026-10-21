-- Prove2me | solution 1 for RelSmoothFOM.DOptimal.proposition_1_1_a_iii
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:41:24.904254+00:00
-- url     : https://prove2.me/submissions/9781dca4-9eaf-4a7f-a02e-56dc0a6b2cad

import Mathlib
import Definitions.Def_RelSmoothFOM_DOptimal_Setting

set_option autoImplicit false

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (U : Set E) (hU : IsOpen U) (hUc : Convex ℝ U)
    (f h : E → ℝ) (hfc : ConvexOn ℝ U f) (hhc : ConvexOn ℝ U h)
    (hfd : ∀ x ∈ U, DifferentiableAt ℝ f x)
    (hhd : ∀ x ∈ U, DifferentiableAt ℝ h x)
    (hf2 : ∀ x ∈ U, DifferentiableAt ℝ (fderiv ℝ f) x)
    (hh2 : ∀ x ∈ U, DifferentiableAt ℝ (fderiv ℝ h) x)
    (L : ℝ)
    (hess : ∀ x ∈ U, ∀ v : E,
      fderiv ℝ (fderiv ℝ f) x v v ≤
        L * fderiv ℝ (fderiv ℝ h) x v v) :
    ∀ x ∈ U, ∀ y ∈ U,
      f y ≤ f x + fderiv ℝ f x (y - x) + L * RelSmoothFOM.PrimalGrad.bregman h y x := by
  intro x hx y hy
  set v : E := y - x with hv
  set z : ℝ → E := fun s => x + s • v with hzdef
  have hz : ∀ s ∈ Set.Icc (0 : ℝ) 1, z s ∈ U := fun s hs => hUc.add_smul_sub_mem hx hy hs
  have hzd : ∀ s, HasDerivAt z v s := by
    intro s
    have := ((hasDerivAt_id' s).smul_const v).const_add x
    rw [one_smul] at this
    exact this
  set g : E → ℝ := fun e => f e - L * h e with hg_def
  set G' : E → (E →L[ℝ] ℝ) := fun e => fderiv ℝ f e - L • fderiv ℝ h e with hG'_def
  have hg : ∀ e ∈ U, HasFDerivAt g (G' e) e := fun e he =>
    (hfd e he).hasFDerivAt.sub ((hhd e he).hasFDerivAt.const_mul L)
  have hG : ∀ e ∈ U, HasFDerivAt G'
      (fderiv ℝ (fderiv ℝ f) e - L • fderiv ℝ (fderiv ℝ h) e) e := fun e he =>
    (hf2 e he).hasFDerivAt.sub ((hh2 e he).hasFDerivAt.const_smul L)
  set ψ : ℝ → ℝ := fun s => g (z s) with hψ
  set θ : ℝ → ℝ := fun s => G' (z s) v with hθ
  have hψd : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt ψ (θ s) s := fun s hs =>
    (hg (z s) (hz s hs)).comp_hasDerivAt s (hzd s)
  have hθd : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt θ
      ((fderiv ℝ (fderiv ℝ f) (z s) v v) - L * (fderiv ℝ (fderiv ℝ h) (z s) v v)) s := by
    intro s hs
    have h1 := (hG (z s) (hz s hs)).comp_hasDerivAt s (hzd s)
    have h2 := ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt).comp_hasDerivAt s h1
    have e : (ContinuousLinearMap.apply ℝ ℝ v)
        ((fderiv ℝ (fderiv ℝ f) (z s) - L • fderiv ℝ (fderiv ℝ h) (z s)) v) =
        (fderiv ℝ (fderiv ℝ f) (z s) v v) - L * (fderiv ℝ (fderiv ℝ h) (z s) v v) := by
      simp
    rw [e] at h2
    exact h2
  have hψc : ContinuousOn ψ (Set.Icc 0 1) := fun s hs => (hψd s hs).continuousAt.continuousWithinAt
  have hθc : ContinuousOn θ (Set.Icc 0 1) := fun s hs => (hθd s hs).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope ψ θ zero_lt_one hψc
    (fun s hs => hψd s (Set.Ioo_subset_Icc_self hs))
  have hanti : AntitoneOn θ (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hθc ?_ ?_
    · rw [interior_Icc]
      exact fun s hs => (hθd s (Set.Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      rw [(hθd s (Set.Ioo_subset_Icc_self hs)).deriv]
      have := hess (z s) (hz s (Set.Ioo_subset_Icc_self hs)) v
      linarith
  have h01 : θ ξ ≤ θ 0 := hanti ⟨le_refl _, zero_le_one⟩ (Set.Ioo_subset_Icc_self hξ) hξ.1.le
  have hz0 : z 0 = x := by simp [hzdef]
  have hz1 : z 1 = y := by simp [hzdef, hv]
  have hψ1 : ψ 1 = g y := by simp [hψ, hz1]
  have hψ0 : ψ 0 = g x := by simp [hψ, hz0]
  have hθ0 : θ 0 = fderiv ℝ f x v - L * fderiv ℝ h x v := by simp [hθ, hG'_def, hz0]
  simp only [sub_zero, div_one] at hξeq
  have key : g y - g x ≤ fderiv ℝ f x v - L * fderiv ℝ h x v := by
    rw [← hψ1, ← hψ0, ← hξeq, ← hθ0]; exact h01
  unfold RelSmoothFOM.PrimalGrad.bregman
  simp only [hg_def] at key
  rw [← hv]
  nlinarith [key]
