-- Prove2me | solution 1 for SubstitutePricing.Unified.price_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:12:52.321638+00:00
-- url     : https://prove2.me/submissions/da2938ec-4b18-4c0f-917a-1ac53d7870ca

import Mathlib
import Definitions.Def_SubstitutePricing_Unified_Model
set_option autoImplicit false
open SubstitutePricing.Unified

theorem solution (M : Model) (hM : M.Assumptions) (x : Fin M.n → ℕ)
    (δ : Fin M.n → ℝ) (r : ℝ) :
    (∀ i ∈ M.S x, HasDerivAt (fun s : ℝ => M.P x (M.const s) i)
        (-(1 / M.μ) * M.P x (M.const r) i * M.P0 x (M.const r)) r) ∧
    HasDerivAt (fun s : ℝ => M.P0 x (M.const s))
        ((1 / M.μ) * M.P0 x (M.const r) * (1 - M.P0 x (M.const r))) r ∧
    HasDerivAt (M.xiS x δ)
        (M.lam * ∑ i ∈ M.S x, (M.P x (M.const r) i -
          (1 / M.μ) * M.P x (M.const r) i * M.P0 x (M.const r) * (r - δ i))) r ∧
    M.lam * ∑ i ∈ M.S x, (M.P x (M.const r) i -
          (1 / M.μ) * M.P x (M.const r) i * M.P0 x (M.const r) * (r - δ i)) =
      M.lam * (1 - M.P0 x (M.const r)) - (1 / M.μ) * M.P0 x (M.const r) * M.xiS x δ r := by
  have hμ := hM.mu_pos
  obtain ⟨S, hS⟩ : ∃ S, M.S x = S := ⟨_, rfl⟩
  obtain ⟨E0, hE0⟩ : ∃ E0 : ℝ, E0 = Real.exp (M.u0 / M.μ) := ⟨_, rfl⟩
  obtain ⟨Ej, hEj⟩ : ∃ Ej : Fin M.n → ℝ → ℝ, Ej = fun j s => Real.exp ((M.a j - s) / M.μ) :=
    ⟨_, rfl⟩
  obtain ⟨Den, hDen⟩ : ∃ Den : ℝ → ℝ, Den = fun s => (∑ j ∈ S, Ej j s) + E0 := ⟨_, rfl⟩
  rw [hS]
  have hE0pos : 0 < E0 := by rw [hE0]; exact Real.exp_pos _
  have hEpos : ∀ j s, 0 < Ej j s := fun j s => by rw [hEj]; exact Real.exp_pos _
  have hDenpos : ∀ s, 0 < Den s := by
    intro s
    have : 0 ≤ ∑ j ∈ S, Ej j s := Finset.sum_nonneg (fun j _ => (hEpos j s).le)
    rw [hDen]; show 0 < (∑ j ∈ S, Ej j s) + E0
    linarith
  have hDens : ∀ s, Den s = (∑ j ∈ S, Ej j s) + E0 := fun s => by rw [hDen]
  have hP : ∀ i ∈ S, ∀ s, M.P x (M.const s) i = Ej i s / Den s := by
    intro i hi s
    have hi' : i ∈ M.S x := by rw [hS]; exact hi
    simp only [Model.P, Model.den, Model.const, if_pos hi', hS, if_pos hi, hDens, hEj, hE0]
  have hP0 : ∀ s, M.P0 x (M.const s) = E0 / Den s := by
    intro s
    simp only [Model.P0, Model.den, Model.const, hS, hDens, hEj, hE0]
  have hEd : ∀ j s, HasDerivAt (Ej j) (-(1 / M.μ) * Ej j s) s := by
    intro j s
    have h := (((hasDerivAt_id s).const_sub (M.a j)).div_const M.μ).exp
    have hfun : Ej j = fun t => Real.exp ((M.a j - id t) / M.μ) := by rw [hEj]; rfl
    rw [hfun]
    refine h.congr_deriv ?_
    simp only [id]
    ring
  have hDd : ∀ s, HasDerivAt Den (-(1 / M.μ) * ∑ j ∈ S, Ej j s) s := by
    intro s
    have h := (HasDerivAt.fun_sum (u := S) (fun j _ => hEd j s)).add_const E0
    have hfun : Den = fun t => (∑ j ∈ S, Ej j t) + E0 := hDen
    rw [hfun]
    refine h.congr_deriv ?_
    rw [Finset.mul_sum]
  have hsumP : ∀ s, ∑ i ∈ S, M.P x (M.const s) i = 1 - M.P0 x (M.const s) := by
    intro s
    rw [Finset.sum_congr rfl (fun i hi => hP i hi s), hP0, ← Finset.sum_div]
    have := (hDenpos s).ne'
    field_simp
    rw [hDens]
    ring
  have hPd : ∀ i ∈ S, HasDerivAt (fun s : ℝ => M.P x (M.const s) i)
      (-(1 / M.μ) * M.P x (M.const r) i * M.P0 x (M.const r)) r := by
    intro i hi
    have hfun : (fun s : ℝ => M.P x (M.const s) i) = fun s => Ej i s / Den s := by
      funext s; exact hP i hi s
    rw [hfun]
    have h := (hEd i r).div (hDd r) (hDenpos r).ne'
    refine h.congr_deriv ?_
    rw [hP i hi, hP0]
    have := (hDenpos r).ne'
    have hsplit := hDens r
    field_simp
    rw [hsplit]
    ring
  have hP0d : HasDerivAt (fun s : ℝ => M.P0 x (M.const s))
      ((1 / M.μ) * M.P0 x (M.const r) * (1 - M.P0 x (M.const r))) r := by
    have hfun : (fun s : ℝ => M.P0 x (M.const s)) = fun s => E0 / Den s := by
      funext s; exact hP0 s
    rw [hfun]
    have h := (hasDerivAt_const r E0).div (hDd r) (hDenpos r).ne'
    refine h.congr_deriv ?_
    rw [hP0]
    have := (hDenpos r).ne'
    have hsplit := hDens r
    field_simp
    rw [hsplit]
    ring
  have hxi : HasDerivAt (M.xiS x δ)
      (M.lam * ∑ i ∈ S, (M.P x (M.const r) i -
          (1 / M.μ) * M.P x (M.const r) i * M.P0 x (M.const r) * (r - δ i))) r := by
    have hfun : M.xiS x δ = fun s => ∑ i ∈ S, M.lam * M.P x (M.const s) i * (s - δ i) := by
      funext s; rw [← hS]; rfl
    rw [hfun]
    have h := HasDerivAt.fun_sum (u := S)
      (A := fun i s => M.lam * M.P x (M.const s) i * (s - δ i))
      (A' := fun i => M.lam * (-(1 / M.μ) * M.P x (M.const r) i * M.P0 x (M.const r)) * (r - δ i)
          + M.lam * M.P x (M.const r) i * 1)
      (fun i hi => ((hPd i hi).const_mul M.lam).mul ((hasDerivAt_id r).sub_const (δ i)))
    refine h.congr_deriv ?_
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  refine ⟨hPd, hP0d, hxi, ?_⟩
  have hxir : M.xiS x δ r = ∑ i ∈ S, M.lam * M.P x (M.const r) i * (r - δ i) := by
    rw [← hS]; rfl
  rw [hxir, ← hsumP r]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring
