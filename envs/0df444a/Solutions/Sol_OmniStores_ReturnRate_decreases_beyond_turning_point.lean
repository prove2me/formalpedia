-- Prove2me | solution 1 for OmniStores.ReturnRate.decreases_beyond_turning_point
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:54:37.551732+00:00
-- url     : https://prove2.me/submissions/bb839f48-b14d-411c-88a2-dcdf2cff3dd9

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

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem solution (P : Params ι) (hP : P.Standing)
    (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (S : Finset ι) (n₁ n₂ : ℝ)
    (hn₁ : nStar P γ ≤ n₁) (hn : n₁ < n₂) :
    profit P γ n₂ S < profit P γ n₁ S :=
  OSH.profit_high P hP hγ.1 hn₁ hn S
