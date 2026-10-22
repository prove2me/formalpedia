-- Prove2me | solution 1 for SubstitutePricing.Unified.optimal_price_formula
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:15:03.178982+00:00
-- url     : https://prove2.me/submissions/6a4ef55f-92e3-495c-bc64-08c8cab0b600

import Mathlib
import Definitions.Def_SubstitutePricing_Unified_Model
set_option autoImplicit false
open SubstitutePricing.Unified

theorem EF_pd (M : Model) (hM : M.Assumptions) (x : Fin M.n → ℕ)
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

theorem solution (M : Model) (hM : M.Assumptions) (x : Fin M.n → ℕ)
    (hx : (M.S x).Nonempty) (δ : Fin M.n → ℝ) (r : ℝ) (hr : HasDerivAt (M.xiS x δ) 0 r) :
    r = M.wavg x δ + M.μ / M.P0 x (M.const r) ∧
    M.marginLHS (M.μ / M.P0 x (M.const r)) =
      Real.exp ((M.aW x - M.wavg x δ) / M.μ) := by
  have hμ := hM.mu_pos
  have hlam := hM.lam_pos
  obtain ⟨-, -, hd, hid⟩ := EF_pd M hM x δ r
  have h0 := hr.unique hd
  -- notation
  obtain ⟨S, hS⟩ : ∃ S, M.S x = S := ⟨_, rfl⟩
  have hSne : S.Nonempty := by rw [← hS]; exact hx
  obtain ⟨Den, hDen⟩ : ∃ Den : ℝ, Den = (∑ j ∈ S, Real.exp ((M.a j - r) / M.μ)) + Real.exp (M.u0 / M.μ) :=
    ⟨_, rfl⟩
  have hDenpos : 0 < Den := by
    rw [hDen]
    have : 0 ≤ ∑ j ∈ S, Real.exp ((M.a j - r) / M.μ) :=
      Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)
    have := Real.exp_pos (M.u0 / M.μ)
    linarith
  have hP0 : M.P0 x (M.const r) = Real.exp (M.u0 / M.μ) / Den := by
    simp only [Model.P0, Model.den, Model.const, hS, hDen]
  have hP : ∀ i ∈ S, M.P x (M.const r) i = Real.exp (-r / M.μ) / Den * Real.exp (M.a i / M.μ) := by
    intro i hi
    have hi' : i ∈ M.S x := by rw [hS]; exact hi
    have : Real.exp ((M.a i - r) / M.μ) = Real.exp (-r / M.μ) * Real.exp (M.a i / M.μ) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [Model.P, if_pos hi']
    simp only [Model.den, Model.const, hS]
    rw [this, ← hDen]
    ring
  obtain ⟨W, hW⟩ : ∃ W, W = ∑ i ∈ S, Real.exp (M.a i / M.μ) := ⟨_, rfl⟩
  have hWpos : 0 < W := by
    rw [hW]
    exact Finset.sum_pos (fun i _ => Real.exp_pos _) hSne
  have hwsum : M.wsum x = W := by rw [hW, ← hS]; rfl
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = Real.exp (-r / M.μ) / Den := ⟨_, rfl⟩
  have hκpos : 0 < κ := by rw [hκ]; positivity
  have hsum1 : ∑ i ∈ S, M.P x (M.const r) i = κ * W := by
    rw [Finset.sum_congr rfl (fun i hi => hP i hi), ← hκ, hW, Finset.mul_sum]
  have hexp : ∑ j ∈ S, Real.exp ((M.a j - r) / M.μ) = Real.exp (-r / M.μ) * W := by
    rw [hW, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Real.exp_add]; congr 1; ring
  have hD : Den = Real.exp (-r / M.μ) * W + Real.exp (M.u0 / M.μ) := by rw [hDen, hexp]
  have hκW : κ * W = 1 - M.P0 x (M.const r) := by
    rw [hP0, hκ, div_mul_eq_mul_div, one_sub_div hDenpos.ne']
    congr 1
    linarith
  have hP0pos : 0 < M.P0 x (M.const r) := by rw [hP0]; positivity
  have h1P0 : 0 < 1 - M.P0 x (M.const r) := by rw [← hκW]; positivity
  -- the weighted average
  have hwavg : M.wavg x δ = (∑ i ∈ S, Real.exp (M.a i / M.μ) * δ i) / W := by
    unfold Model.wavg; rw [hwsum, hS]
  have hxi : M.xiS x δ r = M.lam * ((1 - M.P0 x (M.const r)) * (r - M.wavg x δ)) := by
    have e : M.xiS x δ r = ∑ i ∈ S, M.lam * M.P x (M.const r) i * (r - δ i) := by
      rw [← hS]; rfl
    rw [e, Finset.sum_congr rfl (fun i hi => by rw [hP i hi]), ← hκ, hwavg, ← hκW]
    have h2 : ∑ i ∈ S, M.lam * (κ * Real.exp (M.a i / M.μ)) * (r - δ i) =
        M.lam * κ * (W * r - ∑ i ∈ S, Real.exp (M.a i / M.μ) * δ i) := by
      calc ∑ i ∈ S, M.lam * (κ * Real.exp (M.a i / M.μ)) * (r - δ i)
          = ∑ i ∈ S, (M.lam * κ) * (Real.exp (M.a i / M.μ) * r - Real.exp (M.a i / M.μ) * δ i) :=
            Finset.sum_congr rfl (fun i _ => by ring)
        _ = M.lam * κ * (∑ i ∈ S, Real.exp (M.a i / M.μ) * r - ∑ i ∈ S, Real.exp (M.a i / M.μ) * δ i) := by
            rw [← Finset.mul_sum, Finset.sum_sub_distrib]
        _ = M.lam * κ * (W * r - ∑ i ∈ S, Real.exp (M.a i / M.μ) * δ i) := by
            rw [← Finset.sum_mul, ← hW]
    rw [h2]
    have := hWpos.ne'
    field_simp
  have this1 := h0.trans hid
  rw [hxi] at this1
  have key0 : M.lam * (1 - M.P0 x (M.const r)) *
      (1 - (1 / M.μ) * M.P0 x (M.const r) * (r - M.wavg x δ)) = 0 := by
    linear_combination (-1 : ℝ) * this1
  have key : 1 = (1 / M.μ) * M.P0 x (M.const r) * (r - M.wavg x δ) := by
    rcases mul_eq_zero.1 key0 with h | h
    · exfalso; have := mul_pos hlam h1P0; linarith
    · linarith
  have hr_eq : r = M.wavg x δ + M.μ / M.P0 x (M.const r) := by
    have hne := hP0pos.ne'
    have : r - M.wavg x δ = M.μ / M.P0 x (M.const r) := by
      rw [eq_div_iff hne]
      field_simp at key
      linarith
    linarith
  refine ⟨hr_eq, ?_⟩
  unfold Model.marginLHS Model.aW
  rw [hwsum]
  set m := M.μ / M.P0 x (M.const r) with hm
  have e1 : m / M.μ - 1 = κ * W / M.P0 x (M.const r) := by
    rw [hκW, hm]
    have := hP0pos.ne'
    field_simp
  have e2 : Real.exp ((m + M.u0) / M.μ) = Real.exp (m / M.μ) * Real.exp (M.u0 / M.μ) := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (-r / M.μ) * Real.exp (m / M.μ) = Real.exp (-M.wavg x δ / M.μ) := by
    rw [← Real.exp_add]; congr 1; rw [hr_eq]; ring
  have e4 : Real.exp ((M.μ * Real.log W - M.wavg x δ) / M.μ) = W * Real.exp (-M.wavg x δ / M.μ) := by
    have : (M.μ * Real.log W - M.wavg x δ) / M.μ = Real.log W + (-M.wavg x δ / M.μ) := by
      field_simp
      ring
    rw [this, Real.exp_add, Real.exp_log hWpos]
  rw [e1, e2, e4, ← e3, hκ, hP0]
  have hE := (Real.exp_pos (M.u0 / M.μ)).ne'
  have := hDenpos.ne'
  field_simp
