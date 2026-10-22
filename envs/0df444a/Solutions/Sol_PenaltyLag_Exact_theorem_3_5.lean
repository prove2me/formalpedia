-- Prove2me | solution 1 for PenaltyLag.Exact.theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T14:17:00.330084+00:00
-- url     : https://prove2.me/submissions/7697e57d-c6ea-4c19-b0b9-0d2be9658517

import Mathlib
import Definitions.Def_PenaltyLag_Exact_Basic

set_option autoImplicit false

namespace PenaltyLagA3

open PenaltyLag.Asymptotic

noncomputable def psi (r y t : ℝ) : ℝ := (1 / (4 * r)) * (theta (y + 2 * r * t) ^ 2 - y ^ 2)

lemma psi_le {r : ℝ} (hr : 0 < r) (y t u : ℝ) (htu : t ≤ u) :
    psi r y t ≤ y * u + r * u ^ 2 := by
  unfold psi theta
  have key : (max 0 (y + 2 * r * t)) ^ 2 ≤ (y + 2 * r * u) ^ 2 := by
    rcases le_total (y + 2 * r * t) 0 with h | h
    · rw [max_eq_left h]; nlinarith [sq_nonneg (y + 2 * r * u)]
    · rw [max_eq_right h]
      have h2 : y + 2 * r * t ≤ y + 2 * r * u := by nlinarith
      nlinarith
  have h4 : 0 < 4 * r := by linarith
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ h4]
  nlinarith [key]

lemma psi_eq {r : ℝ} (hr : 0 < r) (y t : ℝ) :
    psi r y t = y * max t (-y / (2 * r)) + r * (max t (-y / (2 * r))) ^ 2 := by
  unfold psi theta
  have hr0 : r ≠ 0 := hr.ne'
  rcases le_total 0 (y + 2 * r * t) with h | h
  · have ht : -y / (2 * r) ≤ t := by rw [div_le_iff₀ (by linarith)]; linarith
    rw [max_eq_right h, max_eq_left ht]
    field_simp
    ring
  · have ht : t ≤ -y / (2 * r) := by rw [le_div_iff₀ (by linarith)]; linarith
    rw [max_eq_left h, max_eq_right ht]
    field_simp
    ring

lemma Lr_eq {E : Type*} {m : ℕ} (f₀ : E → ℝ) (f : Fin m → E → ℝ) (r : ℝ) (x : E)
    (y : Mult m) : Lr f₀ f r x y = f₀ x + ∑ i, psi r (y i) (f i x) := by
  unfold Lr psi; rw [Finset.mul_sum]

lemma L0_le_Lr {E : Type*} {m : ℕ} (f₀ : E → ℝ) (f : Fin m → E → ℝ) {r : ℝ} (hr : 0 < r)
    (x : E) (y : Mult m) : L0 f₀ f x y ≤ (Lr f₀ f r x y : EReal) := by
  unfold L0
  split_ifs with hy
  · rw [Lr_eq]
    have hs : ∑ i, y i * f i x ≤ ∑ i, psi r (y i) (f i x) := Finset.sum_le_sum fun i _ => by
      rw [psi_eq hr]
      have h1 : f i x ≤ max (f i x) (-y i / (2 * r)) := le_max_left _ _
      nlinarith [mul_nonneg (hy i) (sub_nonneg.2 h1),
        mul_nonneg hr.le (sq_nonneg (max (f i x) (-y i / (2 * r))))]
    exact EReal.coe_le_coe_iff.2 (by linarith)
  · exact bot_le

lemma g0_le_gr {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) {r : ℝ}
    (hr : 0 < r) (y : Mult m) : g0 X f₀ f y ≤ gr X f₀ f r y := by
  unfold g0 gr
  exact iInf₂_mono fun x _ => L0_le_Lr f₀ f hr x y

lemma dual_le {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) {r : ℝ}
    (hr : 0 < r) : dualValue X f₀ f ≤ ⨆ y, gr X f₀ f r y := by
  unfold dualValue
  exact iSup_mono fun y => g0_le_gr X f₀ f hr y

lemma Lr_le_f0 {E : Type*} {m : ℕ} (f₀ : E → ℝ) (f : Fin m → E → ℝ) {r : ℝ} (hr : 0 < r)
    (x : E) (y : Mult m) (h : ∀ i, f i x ≤ 0) : Lr f₀ f r x y ≤ f₀ x := by
  rw [Lr_eq]
  have hs : ∑ i, psi r (y i) (f i x) ≤ 0 := Finset.sum_nonpos fun i _ => by
    have := psi_le hr (y i) (f i x) 0 (h i)
    simpa using this
  linarith

theorem main {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (hnormal : PenaltyLag.Exact.IsNormal X f₀ f)
    (ybar : Mult m) (hybar : PenaltyLag.Exact.IsDualOptimal X f₀ f r ybar) (xbar : E) :
    PenaltyLag.Exact.IsOptimal X f₀ f xbar ↔
      (xbar ∈ X ∧ ∀ x ∈ X, Lr f₀ f r xbar ybar ≤ Lr f₀ f r x ybar) := by
  have hP : PenaltyLag.Exact.primalValue X f₀ f ≤ gr X f₀ f r ybar := by
    unfold PenaltyLag.Exact.IsNormal at hnormal
    rw [← hnormal, hybar.2]; exact dual_le X f₀ f hr
  constructor
  · rintro ⟨hxX, hxf, hxopt⟩
    refine ⟨hxX, fun x hx => ?_⟩
    have h1 : ((f₀ xbar : ℝ) : EReal) ≤ PenaltyLag.Exact.primalValue X f₀ f := by
      unfold PenaltyLag.Exact.primalValue
      exact le_iInf₂ fun x hx => le_iInf fun hf => EReal.coe_le_coe_iff.2 (hxopt x hx hf)
    have h2 : gr X f₀ f r ybar ≤ (Lr f₀ f r x ybar : EReal) := by
      unfold gr; exact iInf₂_le x hx
    have h3 := Lr_le_f0 f₀ f hr xbar ybar hxf
    have h4 : ((f₀ xbar : ℝ) : EReal) ≤ (Lr f₀ f r x ybar : EReal) := h1.trans (hP.trans h2)
    exact h3.trans (EReal.coe_le_coe_iff.1 h4)
  · rintro ⟨hxX, hmin⟩
    set Lb := Lr f₀ f r xbar ybar with hLb
    have hG : gr X f₀ f r ybar ≤ (Lb : EReal) := by unfold gr; exact iInf₂_le xbar hxX
    set ub : Fin m → ℝ := fun i => max (f i xbar) (-ybar i / (2 * r)) with hub
    have hLbeq : Lb = f₀ xbar + ∑ i, (ybar i * ub i + r * ub i ^ 2) := by
      rw [hLb, Lr_eq]; congr 1; exact Finset.sum_congr rfl fun i _ => psi_eq hr _ _
    have hsum2 : ∑ i, (ybar i * ub i + r * ub i ^ 2) =
        (∑ i, ybar i * ub i) + r * (∑ i, ub i ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    have hS : ∀ ε > 0, r * (∑ i, ub i ^ 2) ≤ 2 * ε := by
      intro ε hε
      have hlt : PenaltyLag.Exact.primalValue X f₀ f < ((Lb + ε : ℝ) : EReal) := by
        refine lt_of_le_of_lt (hP.trans hG) ?_
        exact EReal.coe_lt_coe_iff.2 (by linarith)
      unfold PenaltyLag.Exact.primalValue at hlt
      rw [iInf_lt_iff] at hlt
      obtain ⟨x₁, hx₁⟩ := hlt
      rw [iInf_lt_iff] at hx₁
      obtain ⟨hx₁X, hx₁⟩ := hx₁
      rw [iInf_lt_iff] at hx₁
      obtain ⟨hx₁f, hx₁⟩ := hx₁
      have hf₁ : f₀ x₁ < Lb + ε := EReal.coe_lt_coe_iff.1 hx₁
      have hxmX : (1/2 : ℝ) • x₁ + (1/2 : ℝ) • xbar ∈ X :=
        hX hx₁X hxX (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
      have hf0m : f₀ ((1/2 : ℝ) • x₁ + (1/2 : ℝ) • xbar) ≤ (1/2) * f₀ x₁ + (1/2) * f₀ xbar := by
        have := hf₀.2 hx₁X hxX (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
          (by norm_num)
        simp only [smul_eq_mul] at this
        exact this
      have hfim : ∀ i, f i ((1/2 : ℝ) • x₁ + (1/2 : ℝ) • xbar) ≤ ub i / 2 := by
        intro i
        have := (hf i).2 hx₁X hxX (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
          (by norm_num)
        simp only [smul_eq_mul] at this
        have h1 := hx₁f i
        have h2 : f i xbar ≤ ub i := le_max_left _ _
        linarith
      have hLm : Lr f₀ f r ((1/2 : ℝ) • x₁ + (1/2 : ℝ) • xbar) ybar ≤
          f₀ ((1/2 : ℝ) • x₁ + (1/2 : ℝ) • xbar) +
            ∑ i, (ybar i * (ub i / 2) + r * (ub i / 2) ^ 2) := by
        rw [Lr_eq]
        have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
          psi_le hr (ybar i) (f i ((1/2 : ℝ) • x₁ + (1/2 : ℝ) • xbar)) (ub i / 2) (hfim i)
        linarith
      have hmid := hmin _ hxmX
      have hsum : ∑ i, (ybar i * (ub i / 2) + r * (ub i / 2) ^ 2) =
          (1/2) * (∑ i, ybar i * ub i) + (1/4) * (r * (∑ i, ub i ^ 2)) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      linarith
    have hS0 : (∑ i, ub i ^ 2) ≤ 0 := by
      by_contra h0
      have h := not_le.1 h0
      have hpos := mul_pos hr h
      have := hS (r * (∑ i, ub i ^ 2) / 4) (by linarith)
      linarith
    have hub0 : ∀ i, ub i = 0 := by
      intro i
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (ub i))).1
        (le_antisymm hS0 (Finset.sum_nonneg fun i _ => sq_nonneg _)) i (Finset.mem_univ _)
      simpa using h0
    have hfeas : ∀ i, f i xbar ≤ 0 := fun i => by
      have h2 : f i xbar ≤ ub i := le_max_left _ _
      rw [hub0 i] at h2; exact h2
    have hLf : Lb = f₀ xbar := by
      rw [hLbeq]; simp [hub0]
    refine ⟨hxX, hfeas, fun x hx hxf => ?_⟩
    have h1 := hmin x hx
    have h2 := Lr_le_f0 f₀ f hr x ybar hxf
    linarith

end PenaltyLagA3

open PenaltyLag.Exact in
theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (hnormal : IsNormal X f₀ f)
    (ybar : PenaltyLag.Asymptotic.Mult m) (hybar : IsDualOptimal X f₀ f r ybar) (xbar : E) :
    IsOptimal X f₀ f xbar ↔ (xbar ∈ X ∧ ∀ x ∈ X, PenaltyLag.Asymptotic.Lr f₀ f r xbar ybar ≤ PenaltyLag.Asymptotic.Lr f₀ f r x ybar) := by
  exact PenaltyLagA3.main X hX f₀ f hf₀ hf r hr hnormal ybar hybar xbar
