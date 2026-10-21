-- Prove2me | solution 1 for OmniStores.ReturnRate.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:59:39.21453+00:00
-- url     : https://prove2.me/submissions/01c34475-3a18-458d-accd-08dcff6d5e6a

import Mathlib
import Definitions.Def_OmniStores_ReturnRate_ClosedForms

set_option autoImplicit false
open OmniStores.ReturnRate

namespace OSH

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def nS (P : Params ι) (γ : ℝ) : ℝ := P.t / (2 * (γ * P.hr + P.ho))

noncomputable def cr (P : Params ι) (γ : ℝ) (i : ι) : ℝ :=
  P.k i * γ * P.θ * P.D i - nS P γ * P.ξ * P.α i -
    P.ξ * (1 - γ) * P.β i * P.θ * P.D i -
    P.ξ * P.β i * (P.ho / (γ * P.hr + P.ho)) * (1 - P.θ) * P.D i

noncomputable def gp (P : Params ι) (γ : ℝ) : ℝ :=
  Finset.univ.sum (fun i => max (cr P γ i) 0) - nS P γ * P.ξ * P.Ω0

noncomputable def Del (P : Params ι) (γ : ℝ) (S : Finset ι) : ℝ :=
  S.sum (fun i => cr P γ i) - nS P γ * P.ξ * P.Ω0

noncomputable def uu (P : Params ι) (γ n : ℝ) : ℝ := min (2 * n * ((γ * P.hr + P.ho) / P.t)) 1
noncomputable def ww (P : Params ι) (n : ℝ) : ℝ := min (2 * n * (P.ho / P.t)) 1

noncomputable def E (P : Params ι) (γ n : ℝ) (i : ι) : ℝ :=
  P.k i * γ * P.θ * P.D i * uu P γ n -
    (n * P.ξ * P.α i + P.ξ * P.β i * ((1 - γ) * P.θ * P.D i * uu P γ n +
      (1 - P.θ) * P.D i * ww P n))

lemma min_eq (c n : ℝ) (hn : 0 ≤ n) : 2 * min c (1 / (2 * n)) * n = min (2 * n * c) 1 := by
  rcases hn.eq_or_lt with h | h
  · subst h; simp
  · have h2 : 0 < 2 * n := by positivity
    have : 2 * n * min c (1 / (2 * n)) = min (2 * n * c) (2 * n * (1 / (2 * n))) :=
      mul_min_of_nonneg _ _ h2.le
    rw [show 2 * n * (1 / (2 * n)) = 1 by field_simp] at this
    rw [← this]; ring

lemma uu_zero (P : Params ι) (γ : ℝ) : uu P γ 0 = 0 := by simp [uu]
lemma ww_zero (P : Params ι) : ww P 0 = 0 := by simp [ww]

lemma profit_eq (P : Params ι) (γ n : ℝ) (hn : 0 ≤ n) (S : Finset ι) :
    profit P γ n S = profit P γ 0 ∅ + ∑ i ∈ S, E P γ n i - n * P.ξ * P.Ω0 := by
  have hs : ∀ (S : Finset ι) (n' : ℝ), 0 ≤ n' → profit P γ n' S =
      (∑ i, (P.m i * ((1 - γ) * P.θ * P.D i + (1 - P.θ) * P.D i) - P.k i * γ * P.θ * P.D i))
      + ∑ i ∈ S, P.k i * γ * P.θ * P.D i * uu P γ n'
      - (∑ i ∈ S, (n' * P.ξ * P.α i + P.ξ * P.β i * ((1 - γ) * P.θ * P.D i * uu P γ n' +
          (1 - P.θ) * P.D i * ww P n')) + n' * P.ξ * P.Ω0) := by
    intro S n' hn'
    have h1 : ∀ i, P.k i * γ * dUO P γ n' S i =
        P.k i * γ * P.θ * P.D i - (if i ∈ S then P.k i * γ * P.θ * P.D i * uu P γ n' else 0) := by
      intro i
      unfold dUO
      by_cases hi : i ∈ S
      · simp only [hi, if_true, uu, min_eq _ _ hn']; ring
      · simp only [hi, if_false, sub_zero]; ring
    have h2 : n' * P.ξ * storeSize P γ n' S =
        ∑ i ∈ S, (n' * P.ξ * P.α i + P.ξ * P.β i * ((1 - γ) * P.θ * P.D i * uu P γ n' +
          (1 - P.θ) * P.D i * ww P n')) + n' * P.ξ * P.Ω0 := by
      rcases hn'.eq_or_lt with h | h
      · subst h; simp [storeSize, dUS, dIS, uu, ww]
      · unfold storeSize
        rw [mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        simp only [dUS, dIS, hi, if_true, min_eq _ _ h.le, uu, ww]
        field_simp
    have h3 : ∑ i, (P.m i * ((1 - γ) * P.θ * P.D i + (1 - P.θ) * P.D i) -
        P.k i * γ * dUO P γ n' S i) =
        ∑ i, (P.m i * ((1 - γ) * P.θ * P.D i + (1 - P.θ) * P.D i) - P.k i * γ * P.θ * P.D i)
        + ∑ i ∈ S, P.k i * γ * P.θ * P.D i * uu P γ n' := by
      have : ∀ i, (P.m i * ((1 - γ) * P.θ * P.D i + (1 - P.θ) * P.D i) -
          P.k i * γ * dUO P γ n' S i) =
          (P.m i * ((1 - γ) * P.θ * P.D i + (1 - P.θ) * P.D i) - P.k i * γ * P.θ * P.D i)
          + (if i ∈ S then P.k i * γ * P.θ * P.D i * uu P γ n' else 0) := fun i => by
        rw [h1 i]; ring
      rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib,
        Finset.sum_ite_mem, Finset.univ_inter]
    unfold profit
    rw [h3, h2]
  have e0 := hs ∅ 0 le_rfl
  simp only [Finset.sum_empty, mul_zero, zero_mul, add_zero, sub_zero] at e0
  rw [hs S n hn, e0]
  simp only [E, Finset.sum_sub_distrib]
  ring

end OSH

namespace OSH

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma den_pos (P : Params ι) (hP : P.Standing) {γ : ℝ} (hγ : 0 < γ) : 0 < γ * P.hr + P.ho := by
  obtain ⟨-, -, -, hho, hhr, -⟩ := hP
  positivity

lemma nS_pos (P : Params ι) (hP : P.Standing) {γ : ℝ} (hγ : 0 < γ) : 0 < nS P γ := by
  have := den_pos P hP hγ
  obtain ⟨-, -, -, -, -, -, ht, -⟩ := hP
  unfold nS; positivity

lemma two_nS_a (P : Params ι) (hP : P.Standing) {γ : ℝ} (hγ : 0 < γ) :
    2 * nS P γ * ((γ * P.hr + P.ho) / P.t) = 1 := by
  have := den_pos P hP hγ
  obtain ⟨-, -, -, -, -, -, ht, -⟩ := hP
  unfold nS; field_simp

lemma two_nS_b (P : Params ι) (hP : P.Standing) {γ : ℝ} (hγ : 0 < γ) :
    2 * nS P γ * (P.ho / P.t) = P.ho / (γ * P.hr + P.ho) := by
  have := den_pos P hP hγ
  obtain ⟨-, -, -, -, -, -, ht, -⟩ := hP
  unfold nS; field_simp

lemma b_le_a (P : Params ι) (hP : P.Standing) {γ : ℝ} (hγ : 0 < γ) :
    P.ho / P.t ≤ (γ * P.hr + P.ho) / P.t := by
  obtain ⟨-, -, -, hho, hhr, -, ht, -⟩ := hP
  apply div_le_div_of_nonneg_right _ ht.le
  nlinarith

lemma W_le (P : Params ι) (hP : P.Standing) {γ : ℝ} (hγ : 0 < γ) :
    P.ho / (γ * P.hr + P.ho) ≤ 1 := by
  have hd := den_pos P hP hγ
  obtain ⟨-, -, -, hho, hhr, -⟩ := hP
  rw [div_le_one hd]; nlinarith

lemma E_nS (P : Params ι) (hP : P.Standing) {γ : ℝ} (hγ : 0 < γ) (i : ι) :
    E P γ (nS P γ) i = cr P γ i := by
  have hW := W_le P hP hγ
  unfold E uu ww cr
  rw [two_nS_a P hP hγ, two_nS_b P hP hγ, min_self, min_eq_left hW]
  ring

lemma E_low (P : Params ι) (hP : P.Standing) {γ : ℝ} (hγ : 0 < γ) {n : ℝ} (hn0 : 0 ≤ n)
    (hn : n ≤ nS P γ) (i : ι) :
    E P γ n i = n / nS P γ * E P γ (nS P γ) i := by
  have hpos := nS_pos P hP hγ
  have ha := two_nS_a P hP hγ
  have hb := two_nS_b P hP hγ
  have hW := W_le P hP hγ
  have hd := den_pos P hP hγ
  have hba := b_le_a P hP hγ
  have hs0 : 0 ≤ n / nS P γ := div_nonneg hn0 hpos.le
  have hu : 2 * n * ((γ * P.hr + P.ho) / P.t) = n / nS P γ := by
    rw [eq_div_iff hpos.ne']; linear_combination n * ha
  have hw : 2 * n * (P.ho / P.t) = n / nS P γ * (P.ho / (γ * P.hr + P.ho)) := by
    rw [← hb]; field_simp
  have hu1 : n / nS P γ ≤ 1 := (div_le_one hpos).mpr hn
  have hw1 : n / nS P γ * (P.ho / (γ * P.hr + P.ho)) ≤ 1 := by
    calc _ ≤ 1 * 1 := mul_le_mul hu1 hW (by
            obtain ⟨-, -, -, hho, hhr, -⟩ := hP; positivity) zero_le_one
      _ = 1 := by norm_num
  have hn' : n = n / nS P γ * nS P γ := by field_simp
  unfold E uu ww
  rw [hu, hw, min_eq_left hu1, min_eq_left hw1, ha, hb, min_self, min_eq_left hW]
  linear_combination (-(P.ξ * P.α i)) * hn'

lemma uu_one (P : Params ι) (hP : P.Standing) {γ : ℝ} (hγ : 0 < γ) {n : ℝ}
    (hn : nS P γ ≤ n) : uu P γ n = 1 := by
  have ha := two_nS_a P hP hγ
  have hd := den_pos P hP hγ
  obtain ⟨-, -, -, hho, hhr, -, ht, -⟩ := hP
  have hane : 0 ≤ (γ * P.hr + P.ho) / P.t := by positivity
  unfold uu
  apply min_eq_right
  nlinarith [mul_nonneg hane (sub_nonneg.2 hn)]

lemma E_anti (P : Params ι) (hP : P.Standing) {γ : ℝ} (hγ : 0 < γ) {n₁ n₂ : ℝ}
    (hn₁ : nS P γ ≤ n₁) (hn : n₁ ≤ n₂) (i : ι) : E P γ n₂ i ≤ E P γ n₁ i := by
  have h1 := uu_one P hP hγ hn₁
  have h2 := uu_one P hP hγ (hn₁.trans hn)
  have hP' := hP
  obtain ⟨hθ0, hθ1, hD, hho, hhr, hk, ht, hα, hβ, hΩ, hξ⟩ := hP'
  have hww : ww P n₁ ≤ ww P n₂ := by
    unfold ww
    apply min_le_min_right
    have : 0 ≤ P.ho / P.t := by positivity
    nlinarith
  have h0 : 0 ≤ P.ξ * P.β i * ((1 - P.θ) * P.D i) := by
    have : 0 ≤ 1 - P.θ := by linarith
    have := hD i; have := hβ i; positivity
  have h3 := mul_le_mul_of_nonneg_left hww h0
  have h4 := mul_le_mul_of_nonneg_right hn (show 0 ≤ P.ξ * P.α i from (mul_pos hξ (hα i)).le)
  unfold E
  rw [h1, h2]
  nlinarith

end OSH

namespace OSH

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma profit_nS (P : Params ι) (hP : P.Standing) {γ : ℝ} (hγ : 0 < γ) (S : Finset ι) :
    profit P γ (nS P γ) S = profit P γ 0 ∅ + Del P γ S := by
  rw [profit_eq P γ _ (nS_pos P hP hγ).le S]
  simp only [E_nS P hP hγ, Del]
  ring

lemma profit_low (P : Params ι) (hP : P.Standing) {γ : ℝ} (hγ : 0 < γ) {n : ℝ} (hn0 : 0 ≤ n)
    (hn : n ≤ nS P γ) (S : Finset ι) :
    profit P γ n S = profit P γ 0 ∅ + n / nS P γ * Del P γ S := by
  have hpos := nS_pos P hP hγ
  rw [profit_eq P γ n hn0 S]
  simp only [E_low P hP hγ hn0 hn, E_nS P hP hγ, Del, ← Finset.mul_sum]
  field_simp
  ring

lemma profit_high (P : Params ι) (hP : P.Standing) {γ : ℝ} (hγ : 0 < γ) {n₁ n₂ : ℝ}
    (hn₁ : nS P γ ≤ n₁) (hn : n₁ < n₂) (S : Finset ι) :
    profit P γ n₂ S < profit P γ n₁ S := by
  have hpos := nS_pos P hP hγ
  have hn1 : 0 ≤ n₁ := hpos.le.trans hn₁
  have hn2 : 0 ≤ n₂ := hn1.trans hn.le
  rw [profit_eq P γ n₂ hn2 S, profit_eq P γ n₁ hn1 S]
  have hs : ∑ i ∈ S, E P γ n₂ i ≤ ∑ i ∈ S, E P γ n₁ i :=
    Finset.sum_le_sum (fun i _ => E_anti P hP hγ hn₁ hn.le i)
  obtain ⟨-, -, -, -, -, -, -, -, -, hΩ, hξ⟩ := hP
  have : n₁ * P.ξ * P.Ω0 < n₂ * P.ξ * P.Ω0 := by
    apply mul_lt_mul_of_pos_right _ hΩ
    exact mul_lt_mul_of_pos_right hn hξ
  linarith

lemma profit_bound (P : Params ι) (hP : P.Standing) {γ : ℝ} (hγ : 0 < γ) {n : ℝ} (hn : 0 ≤ n)
    (S : Finset ι) :
    profit P γ n S ≤ max (profit P γ 0 ∅) (profit P γ 0 ∅ + Del P γ S) := by
  have hpos := nS_pos P hP hγ
  rcases le_total n (nS P γ) with h | h
  · rw [profit_low P hP hγ hn h]
    have hs0 : 0 ≤ n / nS P γ := div_nonneg hn hpos.le
    have hs1 : n / nS P γ ≤ 1 := (div_le_one hpos).mpr h
    rcases le_total 0 (Del P γ S) with hD | hD
    · refine le_max_of_le_right ?_
      nlinarith
    · refine le_max_of_le_left ?_
      nlinarith
  · rcases h.eq_or_lt with h' | h'
    · rw [← h', profit_nS P hP hγ]; exact le_max_right _ _
    · have := profit_high P hP hγ le_rfl h' S
      rw [profit_nS P hP hγ] at this
      exact le_max_of_le_right this.le

lemma Del_le_gp (P : Params ι) (γ : ℝ) (S : Finset ι) : Del P γ S ≤ gp P γ := by
  unfold Del gp
  have h1 : ∑ i ∈ S, cr P γ i ≤ ∑ i ∈ S, max (cr P γ i) 0 :=
    Finset.sum_le_sum (fun i _ => le_max_left _ _)
  have h2 : ∑ i ∈ S, max (cr P γ i) 0 ≤ ∑ i, max (cr P γ i) 0 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun i _ _ => le_max_right _ _)
  linarith

lemma gp_eq_Del (P : Params ι) (γ : ℝ) :
    gp P γ = Del P γ (Finset.univ.filter (fun i => 0 < cr P γ i)) := by
  unfold gp Del
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 < cr P γ i
  · rw [if_pos h, max_eq_left h.le]
  · rw [if_neg h, max_eq_right (not_lt.1 h)]

lemma prefers_iff (P : Params ι) (hP : P.Standing) {γ : ℝ} (hγ : 0 < γ) :
    PrefersStores P γ ↔ 0 < gp P γ := by
  constructor
  · rintro ⟨n, S, hn, h⟩
    have := profit_bound P hP hγ hn.le S
    have h2 := Del_le_gp P γ S
    rcases le_total (Del P γ S) 0 with hD | hD
    · have : max (profit P γ 0 ∅) (profit P γ 0 ∅ + Del P γ S) = profit P γ 0 ∅ :=
        max_eq_left (by linarith)
      linarith
    · have : max (profit P γ 0 ∅) (profit P γ 0 ∅ + Del P γ S) = profit P γ 0 ∅ + Del P γ S :=
        max_eq_right (by linarith)
      linarith
  · intro h
    refine ⟨nS P γ, Finset.univ.filter (fun i => 0 < cr P γ i), nS_pos P hP hγ, ?_⟩
    rw [profit_nS P hP hγ, ← gp_eq_Del]
    linarith

lemma optimal_zero (P : Params ι) (hP : P.Standing) {γ : ℝ} (hγ : 0 < γ) (h : gp P γ ≤ 0) :
    IsOptimal P γ 0 ∅ := by
  refine ⟨le_rfl, fun n' S' hn' => ?_⟩
  have := profit_bound P hP hγ hn' S'
  have h2 := Del_le_gp P γ S'
  have : max (profit P γ 0 ∅) (profit P γ 0 ∅ + Del P γ S') = profit P γ 0 ∅ :=
    max_eq_left (by linarith)
  linarith

lemma optimal_star (P : Params ι) (hP : P.Standing) {γ : ℝ} (hγ : 0 < γ) (h : 0 < gp P γ) :
    IsOptimal P γ (nS P γ) (Finset.univ.filter (fun i => 0 < cr P γ i)) := by
  refine ⟨(nS_pos P hP hγ).le, fun n' S' hn' => ?_⟩
  have := profit_bound P hP hγ hn' S'
  have h2 := Del_le_gp P γ S'
  rw [profit_nS P hP hγ, ← gp_eq_Del]
  have : max (profit P γ 0 ∅) (profit P γ 0 ∅ + Del P γ S') ≤ profit P γ 0 ∅ + gp P γ :=
    max_le (by linarith) (by linarith)
  linarith

lemma gp_pos_nonempty (P : Params ι) (hP : P.Standing) {γ : ℝ} (hγ : 0 < γ) (h : 0 < gp P γ) :
    (Finset.univ.filter (fun i => 0 < cr P γ i)).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  rw [gp_eq_Del, hne] at h
  have := nS_pos P hP hγ
  obtain ⟨-, -, -, -, -, -, -, -, -, hΩ, hξ⟩ := hP
  unfold Del at h
  simp only [Finset.sum_empty] at h
  have : 0 < nS P γ * P.ξ * P.Ω0 := by positivity
  linarith

lemma opt_char (P : Params ι) (hP : P.Standing) {γ : ℝ} (hγ : 0 < γ) (h : 0 < gp P γ)
    {n : ℝ} {S : Finset ι} (hopt : IsOptimal P γ n S) :
    n = nS P γ ∧ (∀ i, 0 < cr P γ i → i ∈ S) ∧ (∀ i ∈ S, 0 ≤ cr P γ i) := by
  have hpos := nS_pos P hP hγ
  obtain ⟨hn0, hall⟩ := hopt
  have hstar := hall (nS P γ) (Finset.univ.filter (fun i => 0 < cr P γ i)) hpos.le
  rw [profit_nS P hP hγ, ← gp_eq_Del] at hstar
  have hDel := Del_le_gp P γ S
  have hn : n = nS P γ := by
    rcases lt_trichotomy n (nS P γ) with h1 | h1 | h1
    · exfalso
      rw [profit_low P hP hγ hn0 h1.le] at hstar
      have hs0 : 0 ≤ n / nS P γ := div_nonneg hn0 hpos.le
      have hs1 : n / nS P γ < 1 := (div_lt_one hpos).mpr h1
      nlinarith
    · exact h1
    · exfalso
      have := profit_high P hP hγ le_rfl h1 S
      rw [profit_nS P hP hγ] at this
      linarith
  subst hn
  rw [profit_nS P hP hγ] at hstar
  have hge : gp P γ ≤ Del P γ S := by linarith
  unfold Del gp at hge
  have hnn : ∀ i, 0 ≤ max (cr P γ i) 0 := fun i => le_max_right _ _
  refine ⟨rfl, ?_, ?_⟩
  · intro i hi
    by_contra hiS
    have h1 : ∑ i ∈ S, cr P γ i ≤ ∑ i ∈ S, max (cr P γ i) 0 :=
      Finset.sum_le_sum (fun i _ => le_max_left _ _)
    have h2 : ∑ i ∈ S, max (cr P γ i) 0 < ∑ i, max (cr P γ i) 0 := by
      apply Finset.sum_lt_sum_of_subset (Finset.subset_univ S) (Finset.mem_univ i) hiS
      · rw [max_eq_left hi.le]; exact hi
      · intro j _ _; exact hnn j
    linarith
  · intro i hi
    by_contra hneg
    push Not at hneg
    have h1 : ∑ i ∈ S, cr P γ i < ∑ i ∈ S, max (cr P γ i) 0 := by
      apply Finset.sum_lt_sum (fun j _ => le_max_left _ _)
      exact ⟨i, hi, by rw [max_eq_right hneg.le]; exact hneg⟩
    have h2 : ∑ i ∈ S, max (cr P γ i) 0 ≤ ∑ i, max (cr P γ i) 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun i _ _ => hnn i)
    linarith

end OSH

namespace OSH

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma nS_anti (P : Params ι) (hP : P.Standing) {γ γ' : ℝ} (hγ : 0 < γ) (h : γ ≤ γ') :
    nS P γ' ≤ nS P γ := by
  have hd := den_pos P hP hγ
  obtain ⟨-, -, -, -, hhr, -, ht, -⟩ := hP
  unfold nS
  apply div_le_div_of_nonneg_left ht.le (by positivity)
  nlinarith

lemma nS_strict (P : Params ι) (hP : P.Standing) {γ γ' : ℝ} (hγ : 0 < γ) (h : γ < γ') :
    nS P γ' < nS P γ := by
  have hd := den_pos P hP hγ
  have hd' := den_pos P hP (hγ.trans h)
  obtain ⟨-, -, -, -, hhr, -, ht, -⟩ := hP
  unfold nS
  apply div_lt_div_of_pos_left ht (by positivity)
  nlinarith

lemma cr_diff (P : Params ι) (hP : P.Standing) {γ γ' : ℝ} (hγ : 0 < γ) (h : γ ≤ γ') (i : ι) :
    (nS P γ - nS P γ') * P.ξ * P.α i ≤ cr P γ' i - cr P γ i := by
  have hd := den_pos P hP hγ
  have hd' := den_pos P hP (lt_of_lt_of_le hγ h)
  have hP' := hP
  obtain ⟨hθ0, hθ1, hD, hho, hhr, hk, ht, hα, hβ, hΩ, hξ⟩ := hP'
  have hr : P.ho / (γ' * P.hr + P.ho) ≤ P.ho / (γ * P.hr + P.ho) := by
    apply div_le_div_of_nonneg_left hho hd
    nlinarith
  have h1 : 0 ≤ P.k i * P.θ * P.D i * (γ' - γ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (hk i) hθ0) (hD i).le) (by linarith)
  have h2 : 0 ≤ P.ξ * P.β i * P.θ * P.D i * (γ' - γ) :=
    mul_nonneg (by have := hβ i; have := hD i; positivity) (by linarith)
  have h3 : 0 ≤ P.ξ * P.β i * ((1 - P.θ) * P.D i) *
      (P.ho / (γ * P.hr + P.ho) - P.ho / (γ' * P.hr + P.ho)) := by
    apply mul_nonneg _ (by linarith)
    have : 0 ≤ 1 - P.θ := by linarith
    have := hD i; have := hβ i; positivity
  unfold cr
  nlinarith

lemma cr_mono (P : Params ι) (hP : P.Standing) {γ γ' : ℝ} (hγ : 0 < γ) (h : γ ≤ γ') (i : ι) :
    cr P γ i ≤ cr P γ' i := by
  have := cr_diff P hP hγ h i
  have h1 := nS_anti P hP hγ h
  obtain ⟨-, -, -, -, -, -, -, hα, -, -, hξ⟩ := hP
  have : 0 ≤ (nS P γ - nS P γ') * P.ξ * P.α i :=
    mul_nonneg (mul_nonneg (by linarith) hξ.le) (hα i).le
  linarith

lemma cr_strict (P : Params ι) (hP : P.Standing) {γ γ' : ℝ} (hγ : 0 < γ) (h : γ < γ') (i : ι) :
    cr P γ i < cr P γ' i := by
  have := cr_diff P hP hγ h.le i
  have h1 := nS_strict P hP hγ h
  obtain ⟨-, -, -, -, -, -, -, hα, -, -, hξ⟩ := hP
  have : 0 < (nS P γ - nS P γ') * P.ξ * P.α i :=
    mul_pos (mul_pos (by linarith) hξ) (hα i)
  linarith

lemma gp_mono (P : Params ι) (hP : P.Standing) :
    MonotoneOn (gp P) (Set.Ioi 0) := by
  intro γ hγ γ' hγ' h
  have hγ : 0 < γ := hγ
  have h1 : ∑ i, max (cr P γ i) 0 ≤ ∑ i, max (cr P γ' i) 0 :=
    Finset.sum_le_sum (fun i _ => max_le_max (cr_mono P hP hγ h i) le_rfl)
  have h2 := nS_anti P hP hγ h
  obtain ⟨-, -, -, -, -, -, -, -, -, hΩ, hξ⟩ := hP
  have : nS P γ' * P.ξ * P.Ω0 ≤ nS P γ * P.ξ * P.Ω0 := by
    apply mul_le_mul_of_nonneg_right _ hΩ.le
    exact mul_le_mul_of_nonneg_right h2 hξ.le
  unfold gp
  linarith

lemma gp_cont (P : Params ι) (hP : P.Standing) : ContinuousOn (gp P) (Set.Ioi 0) := by
  have hd : ∀ x ∈ Set.Ioi (0:ℝ), x * P.hr + P.ho ≠ 0 := fun x hx => (den_pos P hP hx).ne'
  have hd2 : ∀ x ∈ Set.Ioi (0:ℝ), 2 * (x * P.hr + P.ho) ≠ 0 := fun x hx => by
    have := den_pos P hP hx; positivity
  have hn : ContinuousOn (nS P) (Set.Ioi 0) := by
    unfold nS
    exact continuousOn_const.div (by fun_prop) hd2
  have hr : ContinuousOn (fun x => P.ho / (x * P.hr + P.ho)) (Set.Ioi 0) :=
    continuousOn_const.div (by fun_prop) hd
  have hc : ∀ i, ContinuousOn (fun γ => cr P γ i) (Set.Ioi 0) := by
    intro i
    unfold cr
    fun_prop
  unfold gp
  apply ContinuousOn.sub
  · exact continuousOn_finsetSum _ (fun i _ => (continuous_id.max continuous_const).comp_continuousOn (hc i))
  · fun_prop

lemma exists_threshold (g : ℝ → ℝ) (hmono : MonotoneOn g (Set.Ioi 0))
    (hcont : ContinuousOn g (Set.Ioi 0)) :
    ∃ G : ℝ, ∀ γ ∈ Set.Ioo (0 : ℝ) 1, (0 < g γ ↔ G < γ) := by
  by_cases h : ∃ γ0 ∈ Set.Ioo (0 : ℝ) 1, g γ0 ≤ 0
  · obtain ⟨γ0, hγ0, hg0⟩ := h
    have hsub : Set.Icc γ0 1 ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le hγ0.1 hx.1
    have hclosed : IsClosed (Set.Icc γ0 1 ∩ g ⁻¹' Set.Iic 0) :=
      (hcont.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hne : (Set.Icc γ0 1 ∩ g ⁻¹' Set.Iic 0).Nonempty :=
      ⟨γ0, ⟨le_rfl, hγ0.2.le⟩, hg0⟩
    have hbdd : BddAbove (Set.Icc γ0 1 ∩ g ⁻¹' Set.Iic 0) :=
      ⟨1, fun x hx => hx.1.2⟩
    have hmem := hclosed.csSup_mem hne hbdd
    set G := sSup (Set.Icc γ0 1 ∩ g ⁻¹' Set.Iic 0) with hG
    have hγ0G : γ0 ≤ G := le_csSup hbdd ⟨⟨le_rfl, hγ0.2.le⟩, hg0⟩
    refine ⟨G, fun γ hγ => ⟨fun hpos => ?_, fun hlt => ?_⟩⟩
    · by_contra hle
      push Not at hle
      have : g γ ≤ g G := hmono hγ.1 (lt_of_lt_of_le hγ0.1 hγ0G) hle
      have h2 : g G ≤ 0 := hmem.2
      linarith
    · by_contra hle
      push Not at hle
      rcases lt_or_ge γ γ0 with h1 | h1
      · linarith
      · have : γ ≤ G := le_csSup hbdd ⟨⟨h1, hγ.2.le⟩, hle⟩
        linarith
  · push Not at h
    refine ⟨0, fun γ hγ => ⟨fun _ => hγ.1, fun _ => h γ hγ⟩⟩

end OSH

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma OSH.hprint (P : Params ι) (hP : P.Standing) {γ : ℝ} (hγ : 0 < γ) :
    IStarPrinted P γ = Finset.univ.filter (fun i => 0 < OSH.cr P γ i) := by
  have hpos := OSH.nS_pos P hP hγ
  have hd := OSH.den_pos P hP hγ
  obtain ⟨-, -, -, -, -, -, ht, -⟩ := hP
  ext i
  simp only [IStarPrinted, Finset.mem_filter, Finset.mem_univ, true_and]
  have hk : OSH.cr P γ i = OSH.nS P γ *
      (P.k i * γ * (2 * (γ * P.hr + P.ho) / P.t) * P.θ * P.D i -
        P.ξ * (P.α i + P.β i * ((2 * P.ho / P.t) * (1 - P.θ) * P.D i +
          (1 - γ) * (2 * (γ * P.hr + P.ho) / P.t) * P.θ * P.D i))) := by
    unfold OSH.cr OSH.nS
    field_simp
    ring
  constructor
  · intro h
    rw [hk]
    exact mul_pos hpos (sub_pos.2 h)
  · intro h
    rw [hk] at h
    exact sub_pos.1 ((mul_pos_iff_of_pos_left hpos).1 h)

theorem solution (P : Params ι) (hP : P.Standing) :
    ∃ G : ℝ, ∀ γ ∈ Set.Ioo (0 : ℝ) 1,
      (PrefersStores P γ ↔ G < γ) ∧
      (G < γ →
        IsOptimal P γ (P.t / (2 * (γ * P.hr + P.ho))) (IStarPrinted P γ) ∧
        (IStarPrinted P γ).Nonempty ∧
        ∀ n S, IsOptimal P γ n S →
          n = P.t / (2 * (γ * P.hr + P.ho)) ∧ IStarPrinted P γ ⊆ S) ∧
      (γ ≤ G → IsOptimal P γ 0 ∅) := by
  obtain ⟨G, hG⟩ := OSH.exists_threshold (OSH.gp P) (OSH.gp_mono P hP) (OSH.gp_cont P hP)
  refine ⟨G, fun γ hγ => ?_⟩
  have h0 : 0 < γ := hγ.1
  have hiff := hG γ hγ
  have hprint := OSH.hprint P hP h0
  refine ⟨(OSH.prefers_iff P hP h0).trans hiff, fun hlt => ?_, fun hle => ?_⟩
  · have hgp := hiff.2 hlt
    rw [hprint]
    refine ⟨OSH.optimal_star P hP h0 hgp, OSH.gp_pos_nonempty P hP h0 hgp, ?_⟩
    intro n S hopt
    obtain ⟨h1, h2, -⟩ := OSH.opt_char P hP h0 hgp hopt
    refine ⟨h1, fun i hi => h2 i ?_⟩
    simpa using hi
  · exact OSH.optimal_zero P hP h0 (not_lt.1 (fun h => not_lt.2 hle (hiff.1 h)))
