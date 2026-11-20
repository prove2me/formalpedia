-- Prove2me | solution 1 for TightReleaseSchedules.Stationary.stationary_shift_release_budget
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T17:34:58.569273+00:00
-- url     : https://prove2.me/submissions/cb1d79cd-7c37-446b-aebd-ece19ab90f95

import Definitions.Def_TightReleaseSchedules_Stationary_geometric_algorithm
import Theorems.Thm_TightReleaseSchedules_Stationary_anchored_cross_moments
import Definitions.Def_TightReleaseSchedules_Stationary_multiscale_prior
import Theorems.Thm_TightReleaseSchedules_Stationary_common_lower_error_event
import Mathlib

section
set_option autoImplicit false
open Finset
open TightReleaseSchedules.Stationary

namespace TRS.Dev.GoalUpper

/-- Per-round cost bound: error bound for the deployed head at round index `i`. -/
noncomputable def bnd (G : Finset ℕ) (d : ℕ) (Δ : ℝ) (i : ℕ) : ℝ :=
  if h : (G.filter (· ≤ i)).Nonempty then
    (2 * (d : ℝ) + 1) / (((G.filter (· ≤ i)).max' h : ℕ) : ℝ) else Δ ^ 2

noncomputable def jf (c : ℕ → ℕ) (J i : ℕ) : ℕ :=
  ((Icc 1 J).filter (fun j => c j ≤ i)).sup id

lemma jf_spec (c : ℕ → ℕ) (J i : ℕ) (h : ((Icc 1 J).filter (fun j => c j ≤ i)).Nonempty) :
    1 ≤ jf c J i ∧ jf c J i ≤ J ∧ c (jf c J i) ≤ i := by
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup _ h id
  have : jf c J i = j := hjeq
  rw [this]
  simp only [mem_filter, mem_Icc] at hj
  exact ⟨hj.1.1, hj.1.2, hj.2⟩

lemma le_jf (c : ℕ → ℕ) (J i j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ J) (h3 : c j ≤ i) :
    j ≤ jf c J i := by
  unfold jf
  exact Finset.le_sup (f := id) (by simp [mem_filter, mem_Icc, h1, h2, h3])

lemma jf_zero (c : ℕ → ℕ) (J i : ℕ) (h : ¬ ((Icc 1 J).filter (fun j => c j ≤ i)).Nonempty) :
    jf c J i = 0 := by
  unfold jf
  rw [Finset.not_nonempty_iff_eq_empty] at h
  rw [h]; simp

lemma bnd_eq (T d J : ℕ) (Δ : ℝ) (c : ℕ → ℕ) (hmono : Monotone c) (i : ℕ) (hi : i < T) :
    bnd (((Icc 1 J).image c).filter (· < T)) d Δ i =
      if jf c J i = 0 then Δ ^ 2 else (2 * (d : ℝ) + 1) / (c (jf c J i) : ℝ) := by
  have hG : ((((Icc 1 J).image c).filter (· < T)).filter (· ≤ i)) =
      ((Icc 1 J).filter (fun j => c j ≤ i)).image c := by
    ext n
    simp only [mem_filter, mem_image, mem_Icc]
    constructor
    · rintro ⟨⟨⟨j, hj, rfl⟩, _⟩, hn⟩
      exact ⟨j, ⟨hj, hn⟩, rfl⟩
    · rintro ⟨j, ⟨hj, hn⟩, rfl⟩
      exact ⟨⟨⟨j, hj, rfl⟩, lt_of_le_of_lt hn hi⟩, hn⟩
  unfold bnd
  by_cases hS : ((Icc 1 J).filter (fun j => c j ≤ i)).Nonempty
  · obtain ⟨h1, h2, h3⟩ := jf_spec c J i hS
    have hne : ((((Icc 1 J).image c).filter (· < T)).filter (· ≤ i)).Nonempty := by
      rw [hG]; exact hS.image c
    rw [dif_pos hne, if_neg (by omega)]
    congr 2
    apply le_antisymm
    · apply Finset.max'_le
      intro n hn
      rw [hG] at hn
      obtain ⟨j, hj, rfl⟩ := mem_image.1 hn
      simp only [mem_filter, mem_Icc] at hj
      exact hmono (le_jf c J i j hj.1.1 hj.1.2 hj.2)
    · apply Finset.le_max'
      rw [hG]
      exact mem_image.2 ⟨jf c J i, by simp [mem_filter, mem_Icc, h1, h2, h3], rfl⟩
  · have hne : ¬ ((((Icc 1 J).image c).filter (· < T)).filter (· ≤ i)).Nonempty := by
      rw [hG]; intro h; exact hS (by simpa using h)
    rw [dif_neg hne, if_pos (jf_zero c J i hS)]


lemma mid_term (x y r : ℝ) (hr : 1 ≤ r) (hx : r ≤ x) (hy : y ≤ r * x + 1) :
    (y - x) / x ≤ r - 1 + 1 / r := by
  have hx0 : 0 < x := by linarith
  rw [div_le_iff₀ hx0]
  have h1 : 1 ≤ 1 / r * x := by
    rw [one_div, inv_mul_eq_div, one_le_div (by linarith)]; exact hx
  nlinarith

lemma fiber_card_zero (c : ℕ → ℕ) (J T : ℕ) (hJ : 1 ≤ J) :
    (((range T).filter (fun i => jf c J i = 0)).card : ℝ) ≤ (c 1 : ℝ) := by
  have : ((range T).filter (fun i => jf c J i = 0)).card ≤ c 1 := by
    calc _ ≤ (range (c 1)).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [mem_filter, mem_range] at hi ⊢
          by_contra hcon
          have := le_jf c J i 1 le_rfl hJ (by omega)
          omega
      _ = c 1 := card_range _
  exact_mod_cast this

lemma fiber_card_mid (c : ℕ → ℕ) (J T j : ℕ) (hj1 : 1 ≤ j) (hj2 : j < J) (hmono : Monotone c) :
    (((range T).filter (fun i => jf c J i = j)).card : ℝ) ≤ (c (j + 1) : ℝ) - c j := by
  have : ((range T).filter (fun i => jf c J i = j)).card ≤ c (j + 1) - c j := by
    calc _ ≤ (Ico (c j) (c (j + 1))).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [mem_filter, mem_range, mem_Ico] at hi ⊢
          obtain ⟨_, hi⟩ := hi
          have hS : ((Icc 1 J).filter (fun j => c j ≤ i)).Nonempty := by
            by_contra hn
            have := jf_zero c J i hn
            omega
          obtain ⟨_, _, h3⟩ := jf_spec c J i hS
          rw [hi] at h3
          refine ⟨h3, ?_⟩
          by_contra hcon
          have := le_jf c J i (j + 1) (by omega) (by omega) (by omega)
          omega
      _ = c (j + 1) - c j := Nat.card_Ico _ _
  have h2 : c j ≤ c (j + 1) := hmono (Nat.le_succ j)
  have := (Nat.cast_le (α := ℝ)).2 this
  rwa [Nat.cast_sub h2] at this

lemma fiber_card_last (c : ℕ → ℕ) (J T : ℕ) (hJ : 1 ≤ J) (r : ℝ) (hr : 1 ≤ r) (hTr : (T : ℝ) ≤ r * c J) :
    (((range T).filter (fun i => jf c J i = J)).card : ℝ) ≤ (r - 1) * (c J : ℝ) := by
  have : ((range T).filter (fun i => jf c J i = J)).card ≤ T - c J := by
    calc _ ≤ (Ico (c J) T).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [mem_filter, mem_range, mem_Ico] at hi ⊢
          obtain ⟨hiT, hi⟩ := hi
          have hS : ((Icc 1 J).filter (fun j => c j ≤ i)).Nonempty := by
            by_contra hn
            have := jf_zero c J i hn
            omega
          obtain ⟨_, _, h3⟩ := jf_spec c J i hS
          rw [hi] at h3
          exact ⟨h3, hiT⟩
      _ = T - c J := Nat.card_Ico _ _
  rcases le_or_gt (c J) T with h | h
  · have := (Nat.cast_le (α := ℝ)).2 this
    rw [Nat.cast_sub h] at this
    linarith
  · have h0 : T - c J = 0 := by omega
    rw [h0] at this
    have : ((range T).filter (fun i => jf c J i = J)).card = 0 := by omega
    rw [this]
    have : (T : ℝ) < c J := by exact_mod_cast h
    have : (0:ℝ) ≤ (r - 1) * c J := by exact mul_nonneg (by linarith) (Nat.cast_nonneg _)
    simpa using this


noncomputable def Fv (d : ℕ) (Δ : ℝ) (c : ℕ → ℕ) (j : ℕ) : ℝ :=
  if j = 0 then Δ ^ 2 else (2 * (d : ℝ) + 1) / (c j : ℝ)

lemma sum_bnd_le (T d K : ℕ) (Δ α r : ℝ) (c : ℕ → ℕ)
    (hd : 1 ≤ d) (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1) (hα : 1 ≤ α) (hr : 1 ≤ r)
    (hmono : Monotone c)
    (hc1 : ∀ j, α * r ^ j ≤ c j) (hc2 : ∀ j, (c j : ℝ) ≤ α * r ^ j + 1)
    (hT : (T : ℝ) = α * r ^ (K + 2)) (hαΔ : Δ ^ 2 * α = d) :
    ∑ i ∈ range T, bnd (((Icc 1 (K + 1)).image c).filter (· < T)) d Δ i ≤
      d * (r + 1) + 3 * d * ((K + 1) * (r - 1 + 1 / r)) := by
  have hJ : 1 ≤ K + 1 := by omega
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hΔ2 : Δ ^ 2 ≤ 1 := by nlinarith
  have hΔ2' : 0 ≤ Δ ^ 2 := by positivity
  have h1 : ∑ i ∈ range T, bnd (((Icc 1 (K + 1)).image c).filter (· < T)) d Δ i
      = ∑ i ∈ range T, Fv d Δ c (jf c (K + 1) i) := by
    apply sum_congr rfl
    intro i hi
    rw [bnd_eq T d (K + 1) Δ c hmono i (mem_range.1 hi)]
    rfl
  have h2 : ∑ i ∈ range T, Fv d Δ c (jf c (K + 1) i) =
      ∑ j ∈ range (K + 2), (((range T).filter (fun i => jf c (K + 1) i = j)).card : ℝ) *
        Fv d Δ c j := by
    rw [← sum_fiberwise_of_maps_to' (s := range T) (t := range (K + 2)) (g := jf c (K + 1))]
    · apply sum_congr rfl
      intro j _
      rw [sum_const, nsmul_eq_mul]
    · intro i _
      rw [mem_range]
      by_cases hS : ((Icc 1 (K + 1)).filter (fun j => c j ≤ i)).Nonempty
      · have := (jf_spec c (K + 1) i hS).2.1; omega
      · rw [jf_zero c (K + 1) i hS]; omega
  have hcpos : ∀ j, 1 ≤ j → (1 : ℝ) ≤ c j := by
    intro j hj
    have : (1 : ℝ) ≤ α * r ^ j := by
      have := one_le_pow₀ (M₀ := ℝ) hr (n := j)
      nlinarith
    linarith [hc1 j]
  have hcr : ∀ j, 1 ≤ j → r ≤ c j := by
    intro j hj
    have : r ≤ α * r ^ j := by
      have h1 : r ^ 1 ≤ r ^ j := pow_le_pow_right₀ hr hj
      rw [pow_one] at h1
      nlinarith
    linarith [hc1 j]
  rw [h1, h2, sum_range_succ, sum_range_succ']
  -- term 0
  have t0 : (((range T).filter (fun i => jf c (K + 1) i = 0)).card : ℝ) * Fv d Δ c 0 ≤
      d * r + d := by
    have := fiber_card_zero c (K + 1) T hJ
    have hc1' := hc2 1
    rw [pow_one] at hc1'
    simp only [Fv, if_true]
    calc _ ≤ (c 1 : ℝ) * Δ ^ 2 := mul_le_mul_of_nonneg_right this hΔ2'
      _ ≤ (α * r + 1) * Δ ^ 2 := mul_le_mul_of_nonneg_right hc1' hΔ2'
      _ = Δ ^ 2 * α * r + Δ ^ 2 := by ring
      _ ≤ d * r + d := by rw [hαΔ]; linarith
  -- middle terms
  have tm : ∀ j ∈ range K, (((range T).filter (fun i => jf c (K + 1) i = j + 1)).card : ℝ) *
      Fv d Δ c (j + 1) ≤ (2 * (d : ℝ) + 1) * (r - 1 + 1 / r) := by
    intro j hj
    rw [mem_range] at hj
    have hcard := fiber_card_mid c (K + 1) T (j + 1) (by omega) (by omega) hmono
    have hx := hcr (j + 1) (by omega)
    have hxpos := hcpos (j + 1) (by omega)
    have hy : (c (j + 1 + 1) : ℝ) ≤ r * c (j + 1) + 1 := by
      have := hc2 (j + 1 + 1)
      have h3 := hc1 (j + 1)
      calc (c (j + 1 + 1) : ℝ) ≤ α * r ^ (j + 1 + 1) + 1 := this
        _ = r * (α * r ^ (j + 1)) + 1 := by ring
        _ ≤ r * c (j + 1) + 1 := by nlinarith
    have hm := mid_term (c (j + 1)) (c (j + 1 + 1)) r hr hx hy
    simp only [Fv, if_neg (Nat.succ_ne_zero j)]
    have h2d : (0 : ℝ) ≤ 2 * (d : ℝ) + 1 := by positivity
    calc (((range T).filter (fun i => jf c (K + 1) i = j + 1)).card : ℝ) *
          ((2 * (d : ℝ) + 1) / (c (j + 1) : ℝ))
        ≤ ((c (j + 1 + 1) : ℝ) - c (j + 1)) * ((2 * (d : ℝ) + 1) / (c (j + 1) : ℝ)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (2 * (d : ℝ) + 1) * (((c (j + 1 + 1) : ℝ) - c (j + 1)) / (c (j + 1) : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hm h2d
  -- last term
  have tl : (((range T).filter (fun i => jf c (K + 1) i = K + 1)).card : ℝ) *
      Fv d Δ c (K + 1) ≤ (2 * (d : ℝ) + 1) * (r - 1) := by
    have hTr : (T : ℝ) ≤ r * c (K + 1) := by
      rw [hT]
      have := hc1 (K + 1)
      calc α * r ^ (K + 2) = r * (α * r ^ (K + 1)) := by ring
        _ ≤ r * c (K + 1) := by nlinarith
    have hcard := fiber_card_last c (K + 1) T hJ r hr hTr
    have hxpos := hcpos (K + 1) (by omega)
    simp only [Fv, if_neg (Nat.succ_ne_zero K)]
    have h2d : (0 : ℝ) ≤ 2 * (d : ℝ) + 1 := by positivity
    calc (((range T).filter (fun i => jf c (K + 1) i = K + 1)).card : ℝ) *
          ((2 * (d : ℝ) + 1) / (c (K + 1) : ℝ))
        ≤ ((r - 1) * (c (K + 1) : ℝ)) * ((2 * (d : ℝ) + 1) / (c (K + 1) : ℝ)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (2 * (d : ℝ) + 1) * (r - 1) := by field_simp
  have hsum := sum_le_sum tm
  rw [sum_const, card_range, nsmul_eq_mul] at hsum
  have hu : r - 1 ≤ r - 1 + 1 / r := by
    have : (0 : ℝ) ≤ 1 / r := by positivity
    linarith
  have hu0 : 0 ≤ r - 1 := by linarith
  have h3d : 2 * (d : ℝ) + 1 ≤ 3 * d := by linarith
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hurr : (0 : ℝ) ≤ r - 1 + 1 / r := le_trans hu0 hu
  have : (2 * (d : ℝ) + 1) * ((K : ℝ) * (r - 1 + 1 / r) + (r - 1)) ≤
      3 * d * ((K + 1) * (r - 1 + 1 / r)) := by
    have : (K : ℝ) * (r - 1 + 1 / r) + (r - 1) ≤ (K + 1) * (r - 1 + 1 / r) := by nlinarith
    calc _ ≤ (2 * (d : ℝ) + 1) * ((K + 1) * (r - 1 + 1 / r)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right h3d (by positivity)
  nlinarith


lemma u_le (r : ℝ) (hr : 1 ≤ r) : r - 1 + 1 / r ≤ r := by
  have : 1 / r ≤ 1 := by rw [div_le_one (by linarith)]; exact hr
  linarith

lemma ineqB1 (d J r : ℝ) (hd : 0 ≤ d) (hJ : 0 ≤ J) (hr : 2.7 ≤ r) :
    d * (r + 1) + 3 * d * (J * (r - 1 + 1 / r)) ≤ 10 * d * (1 + (J + 1) * (r - 1)) := by
  have hu := u_le r (by linarith)
  have h1 : r + 1 + 3 * (J * (r - 1 + 1 / r)) ≤ 10 * (1 + (J + 1) * (r - 1)) := by
    have : J * (r - 1 + 1 / r) ≤ J * r := mul_le_mul_of_nonneg_left hu hJ
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hd]

lemma ineqB2 (d J L r : ℝ) (hd : 0 ≤ d) (hJ : 0 ≤ J) (hJL : J ≤ L) (hr1 : 1 ≤ r)
    (hr : r ≤ 2.72) :
    d * (r + 1) + 3 * d * (J * (r - 1 + 1 / r)) ≤ 10 * d * (1 + L) := by
  have hu := u_le r hr1
  have h1 : r + 1 + 3 * (J * (r - 1 + 1 / r)) ≤ 10 * (1 + L) := by
    have : J * (r - 1 + 1 / r) ≤ J * r := mul_le_mul_of_nonneg_left hu hJ
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hd]

lemma grid_eq (T d B : ℕ) (Δ : ℝ) : geometricGrid T d B Δ =
    ((Icc 1 (geometricCount T d B Δ)).image
      (fun j : ℕ => ⌈((d : ℝ) / Δ ^ 2) *
        (effectiveHorizon T d Δ ^ (1 / ((geometricCount T d B Δ : ℕ) + 1 : ℝ))) ^ j⌉₊)).filter
      (· < T) := rfl

lemma bnd_empty (d : ℕ) (Δ : ℝ) (i : ℕ) : bnd (∅ : Finset ℕ) d Δ i = Δ ^ 2 := by
  simp [bnd]

lemma eh_mul (T d : ℕ) (Δ : ℝ) (hd : 0 < d) : (d : ℝ) * effectiveHorizon T d Δ = T * Δ ^ 2 := by
  unfold effectiveHorizon
  have : (d : ℝ) ≠ 0 := by positivity
  field_simp


lemma rate_of_lt (B : ℕ) (m : ℝ) (hm : m < 1) : releaseRate B m = m := by
  unfold releaseRate; rw [if_pos hm]

lemma rate_of_ge (B : ℕ) (m : ℝ) (hm : 1 ≤ m) :
    releaseRate B m = 1 + (B + 1 : ℝ) * (m ^ (1 / (B + 1 : ℝ)) - 1) := by
  unfold releaseRate; rw [if_neg (not_lt.2 hm)]

lemma rate_ge_one (B : ℕ) (m : ℝ) (hm : 1 ≤ m) : 1 ≤ releaseRate B m := by
  rw [rate_of_ge B m hm]
  have : 1 ≤ m ^ (1 / (B + 1 : ℝ)) := Real.one_le_rpow hm (by positivity)
  have h2 : (0 : ℝ) ≤ (B + 1 : ℝ) := by positivity
  nlinarith

lemma rate_zero (m : ℝ) (hm : 1 ≤ m) : releaseRate 0 m = m := by
  rw [rate_of_ge 0 m hm]; simp

lemma geometricCount_cases (T d B : ℕ) (Δ : ℝ)
    (hA : ¬ (B = 0 ∨ effectiveHorizon T d Δ ≤ Real.exp 1)) :
    (geometricCount T d B Δ = B ∧ ((B : ℝ) + 1) < Real.log (effectiveHorizon T d Δ)) ∨
    (geometricCount T d B Δ = ⌈Real.log (effectiveHorizon T d Δ)⌉₊ - 1 ∧
      ¬ (((B : ℝ) + 1) < Real.log (effectiveHorizon T d Δ))) := by
  unfold geometricCount
  simp only []
  rw [if_neg hA]
  by_cases h : ((B : ℝ) + 1) < Real.log (effectiveHorizon T d Δ)
  · left; rw [if_pos h]; exact ⟨rfl, h⟩
  · right; rw [if_neg h]; exact ⟨rfl, h⟩

lemma grid_sum_small (T d B : ℕ) (hd : 0 < d) (Δ : ℝ)
    (hA : B = 0 ∨ effectiveHorizon T d Δ ≤ Real.exp 1) (hm0 : 0 < effectiveHorizon T d Δ) :
    ∑ i ∈ range T, bnd (geometricGrid T d B Δ) d Δ i ≤
      10 * d * releaseRate B (effectiveHorizon T d Δ) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hJ : geometricCount T d B Δ = 0 := by
    unfold geometricCount; simp only []; rw [if_pos hA]
  rw [grid_eq, hJ]
  have hE : ∀ f : ℕ → ℕ, ((Icc 1 0).image f).filter (· < T) = ∅ := by
    intro f; simp
  rw [hE]
  simp only [bnd_empty, sum_const, card_range, nsmul_eq_mul]
  have h1 := eh_mul T d Δ hd
  set m := effectiveHorizon T d Δ with hm
  have hmr : m ≤ 10 * releaseRate B m := by
    by_cases hm1 : m < 1
    · rw [rate_of_lt B m hm1]; linarith
    · push_neg at hm1
      rcases hA with h0 | h0
      · subst h0; rw [rate_zero m hm1]; linarith
      · have := rate_ge_one B m hm1
        have := Real.exp_one_lt_d9
        linarith
  rw [← h1]
  nlinarith


lemma rpow_exp_form (m y : ℝ) (hm : 0 < m) : m ^ y = Real.exp (Real.log m * y) := by
  rw [Real.rpow_def_of_pos hm]

lemma grid_sum_large (T d B : ℕ) (hT : 0 < T) (hd : 0 < d) (Δ : ℝ) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1)
    (hA : ¬ (B = 0 ∨ effectiveHorizon T d Δ ≤ Real.exp 1)) :
    ∑ i ∈ range T, bnd (geometricGrid T d B Δ) d Δ i ≤
      10 * d * releaseRate B (effectiveHorizon T d Δ) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hm0 : 0 < effectiveHorizon T d Δ := by unfold effectiveHorizon; positivity
  have hcases := geometricCount_cases T d B Δ hA
  push_neg at hA
  obtain ⟨hB0, hme⟩ := hA
  set m := effectiveHorizon T d Δ with hm
  have hL1 : 1 < Real.log m := by
    rw [Real.lt_log_iff_exp_lt hm0]; exact hme
  have hm1 : 1 ≤ m := by
    have := Real.exp_one_gt_d9
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  -- J = K + 1
  obtain ⟨K, hK⟩ : ∃ K, geometricCount T d B Δ = K + 1 := by
    rcases hcases with ⟨h, _⟩ | ⟨h, _⟩
    · exact ⟨B - 1, by omega⟩
    · refine ⟨⌈Real.log m⌉₊ - 2, ?_⟩
      have : 1 < ⌈Real.log m⌉₊ := by
        rw [Nat.lt_ceil]; exact_mod_cast hL1
      omega
  rw [grid_eq, hK]
  set r : ℝ := m ^ (1 / (((K + 1 : ℕ) : ℝ) + 1)) with hr
  have hKc : (((K + 1 : ℕ) : ℝ) + 1) = (K : ℝ) + 2 := by push_cast; ring
  have hr1 : 1 ≤ r := by
    rw [hr]; exact Real.one_le_rpow hm1 (by positivity)
  have hrpow : r ^ (K + 2) = m := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hm0.le]
    have : (1 / (((K + 1 : ℕ) : ℝ) + 1)) * ((K + 2 : ℕ) : ℝ) = 1 := by
      rw [hKc]; push_cast; field_simp
    rw [this, Real.rpow_one]
  have hα1 : 1 ≤ (d : ℝ) / Δ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hαpos : 0 < (d : ℝ) / Δ ^ 2 := by linarith
  have hmain := sum_bnd_le T d K Δ ((d : ℝ) / Δ ^ 2) r
    (fun j : ℕ => ⌈((d : ℝ) / Δ ^ 2) * r ^ j⌉₊) hd hΔ hΔ₁ hα1 hr1
    (fun a b hab => Nat.ceil_mono (by
      have := pow_le_pow_right₀ hr1 hab
      nlinarith))
    (fun j => Nat.le_ceil _)
    (fun j => (Nat.ceil_lt_add_one (by positivity)).le)
    (by
      rw [hrpow, hm]
      have := eh_mul T d Δ hd
      rw [hm] at *
      field_simp
      linarith)
    (by field_simp)
  refine le_trans hmain ?_
  have hcast : (((K + 1 : ℕ) : ℝ)) = (K : ℝ) + 1 := by push_cast; ring
  rcases hcases with ⟨hJB, hlt⟩ | ⟨hJc, hnlt⟩
  · -- J = B
    have hBK : (B : ℝ) = (K : ℝ) + 1 := by
      have : B = K + 1 := by omega
      rw [this]; push_cast; ring
    have hrate := rate_of_ge B m hm1
    have hrB : m ^ (1 / ((B : ℝ) + 1)) = r := by
      rw [hr, hBK]; congr 2; push_cast; ring
    rw [hrate, hrB, hBK]
    have hr27 : 2.7 ≤ r := by
      have h1 : Real.exp 1 < r := by
        rw [hr, rpow_exp_form m _ hm0]
        apply Real.exp_lt_exp.2
        rw [hKc]
        have : (B : ℝ) + 1 = (K : ℝ) + 2 := by rw [hBK]; ring
        rw [← this]
        rw [mul_one_div, lt_div_iff₀ (by positivity)]
        linarith
      have := Real.exp_one_gt_d9
      linarith
    have := ineqB1 d ((K : ℝ) + 1) r (by positivity) (by positivity) hr27
    have e2 : ((K : ℝ) + 1 + 1) = (K : ℝ) + 1 + 1 := rfl
    convert this using 2 <;> ring_nf
  · -- J = ⌈log m⌉ - 1
    have hce : ⌈Real.log m⌉₊ = K + 2 := by
      have : 1 < ⌈Real.log m⌉₊ := by
        rw [Nat.lt_ceil]; exact_mod_cast hL1
      omega
    have hceR : (⌈Real.log m⌉₊ : ℝ) = (K : ℝ) + 2 := by rw [hce]; push_cast; ring
    have hJL : (K : ℝ) + 1 ≤ Real.log m := by
      have := Nat.ceil_lt_add_one (show 0 ≤ Real.log m by linarith)
      rw [hceR] at this
      linarith
    have hr272 : r ≤ 2.72 := by
      have h1 : r ≤ Real.exp 1 := by
        rw [hr, rpow_exp_form m _ hm0]
        apply Real.exp_le_exp.2
        rw [hKc, ← hceR, mul_one_div, div_le_one (by positivity)]
        exact Nat.le_ceil _
      have := Real.exp_one_lt_d9
      linarith
    have hrate := rate_of_ge B m hm1
    have hrge : 1 + Real.log m ≤ releaseRate B m := by
      rw [hrate]
      have h1 : 1 + Real.log m * (1 / ((B : ℝ) + 1)) ≤ m ^ (1 / ((B : ℝ) + 1)) := by
        rw [rpow_exp_form m _ hm0]
        have := Real.add_one_le_exp (Real.log m * (1 / ((B : ℝ) + 1)))
        linarith
      have hB1 : (0 : ℝ) < (B : ℝ) + 1 := by positivity
      have h2 : Real.log m ≤ ((B : ℝ) + 1) * (m ^ (1 / ((B : ℝ) + 1)) - 1) := by
        have := mul_le_mul_of_nonneg_left h1 hB1.le
        have h3 : ((B : ℝ) + 1) * (Real.log m * (1 / ((B : ℝ) + 1))) = Real.log m := by
          field_simp
        nlinarith
      linarith
    have := ineqB2 d ((K : ℝ) + 1) (Real.log m) r (by positivity) (by positivity) hJL hr1 hr272
    calc _ ≤ 10 * (d : ℝ) * (1 + Real.log m) := by
          exact this
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left hrge (by positivity)


theorem grid_sum_le (T d B : ℕ) (hT : 0 < T) (hd : 0 < d) (Δ : ℝ) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1) :
    ∑ i ∈ range T, bnd (geometricGrid T d B Δ) d Δ i ≤
      10 * d * releaseRate B (effectiveHorizon T d Δ) := by
  by_cases hA : B = 0 ∨ effectiveHorizon T d Δ ≤ Real.exp 1
  · exact grid_sum_small T d B hd Δ hA (by unfold effectiveHorizon; positivity)
  · exact grid_sum_large T d B hT hd Δ hΔ hΔ₁ hA

end TRS.Dev.GoalUpper
end

section
set_option autoImplicit false
open Finset
open TightReleaseSchedules.Stationary

namespace TRS.Dev.GoalUpper

/-- The `j`-th date of the sorted grid, padded by `T`. -/
def sd (T : ℕ) (G : Finset ℕ) (j : ℕ) : ℕ := (G.sort (· ≤ ·))[j]?.getD T

lemma sort_pairwise_lt (G : Finset ℕ) : (G.sort (· ≤ ·)).Pairwise (· < ·) := by
  have h1 := Finset.pairwise_sort G (· ≤ ·)
  have h2 := Finset.sort_nodup G (· ≤ ·)
  exact (h1.and h2).imp (fun ⟨a, b⟩ => lt_of_le_of_ne a b)

lemma sd_of_lt (T : ℕ) (G : Finset ℕ) (j : ℕ) (h : j < (G.sort (· ≤ ·)).length) :
    sd T G j = (G.sort (· ≤ ·))[j] := by
  unfold sd; rw [List.getElem?_eq_getElem h]; rfl

lemma sd_of_ge (T : ℕ) (G : Finset ℕ) (j : ℕ) (h : (G.sort (· ≤ ·)).length ≤ j) :
    sd T G j = T := by
  unfold sd; rw [List.getElem?_eq_none h]; rfl

lemma sd_mem (T : ℕ) (G : Finset ℕ) (j : ℕ) (h : j < (G.sort (· ≤ ·)).length) :
    sd T G j ∈ G := by
  rw [sd_of_lt T G j h, ← Finset.mem_sort (· ≤ ·)]
  exact List.getElem_mem h

lemma sd_le (T : ℕ) (G : Finset ℕ) (hG : ∀ n ∈ G, n < T) (j : ℕ) : sd T G j ≤ T := by
  by_cases h : j < (G.sort (· ≤ ·)).length
  · exact (hG _ (sd_mem T G j h)).le
  · rw [sd_of_ge T G j (not_lt.1 h)]

lemma sd_mono (T : ℕ) (G : Finset ℕ) (hG : ∀ n ∈ G, n < T) {j j' : ℕ} (hj : j ≤ j') :
    sd T G j ≤ sd T G j' := by
  by_cases h' : j' < (G.sort (· ≤ ·)).length
  · have h : j < (G.sort (· ≤ ·)).length := lt_of_le_of_lt hj h'
    rw [sd_of_lt T G j h, sd_of_lt T G j' h']
    rcases hj.eq_or_lt with rfl | hlt
    · exact le_rfl
    · exact ((List.pairwise_iff_getElem.1 (sort_pairwise_lt G)) j j' h h' hlt).le
  · rw [sd_of_ge T G j' (not_lt.1 h')]
    exact sd_le T G hG j

/-- finite fold characterization -/
lemma fold_char {V : Type*} (T B : ℕ) (G : Finset ℕ) (hG : ∀ n ∈ G, n < T)
    (hcard : G.card ≤ B) (θ₀ : V) (H : ℕ → V) (i : ℕ) (hi : i < T) :
    (List.finRange B).foldl (fun w (j : Fin B) => if sd T G j.val ≤ i then H (sd T G j.val) else w) θ₀ =
      if h : (G.filter (· ≤ i)).Nonempty then H ((G.filter (· ≤ i)).max' h) else θ₀ := by
  set l := G.sort (· ≤ ·) with hl
  have hlen : l.length = G.card := Finset.length_sort _
  have hconv : (List.finRange B).foldl
      (fun w (j : Fin B) => if sd T G j.val ≤ i then H (sd T G j.val) else w) θ₀ =
      (List.range B).foldl (fun w (j : ℕ) => if sd T G j ≤ i then H (sd T G j) else w) θ₀ := by
    rw [← List.map_coe_finRange_eq_range, List.foldl_map]
  rw [hconv]
  -- A b : the elements of the first b entries which are ≤ i
  have key : ∀ b, b ≤ B →
      (List.range b).foldl (fun w (j : ℕ) => if sd T G j ≤ i then H (sd T G j) else w) θ₀ =
        if h : (((l.take b).filter (· ≤ i)).toFinset).Nonempty
        then H ((((l.take b).filter (· ≤ i)).toFinset).max' h) else θ₀ := by
    intro b
    induction b with
    | zero => intro _; simp
    | succ b ih =>
      intro hb
      rw [List.range_succ, List.foldl_append, ih (by omega)]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hbl : b < l.length
      · have hs : sd T G b = l[b] := sd_of_lt T G b hbl
        have htake : l.take (b + 1) = l.take b ++ [l[b]] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hbl]; rfl
        have hlt : ∀ x ∈ l.take b, x < l[b] := by
          intro x hx
          have hp := sort_pairwise_lt G
          rw [← hl] at hp
          have hp2 := hp
          rw [← List.take_append_drop b l, List.pairwise_append] at hp2
          apply hp2.2.2 x hx
          have : l[b] ∈ l.drop b := by
            rw [List.mem_iff_getElem]
            exact ⟨0, by simp; omega, by simp⟩
          exact this
        rw [hs]
        by_cases hle : l[b] ≤ i
        · rw [if_pos hle, htake, List.filter_append]
          simp only [List.filter_cons, decide_eq_true_eq, hle, if_true, List.filter_nil]
          rw [dif_pos]
          · congr 1
            apply le_antisymm
            · apply Finset.le_max'
              simp
            · apply Finset.max'_le
              intro x hx
              simp only [List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
                Finset.mem_union, List.mem_toFinset, List.mem_filter, decide_eq_true_eq,
                Finset.mem_insert, Finset.notMem_empty, or_false] at hx
              rcases hx with ⟨hx, _⟩ | hx
              · exact (hlt x hx).le
              · exact hx.le
          · simp
        · rw [if_neg hle, htake, List.filter_append]
          simp only [List.filter_cons, decide_eq_true_eq, hle, if_false, List.filter_nil]
          simp
      · have hs : sd T G b = T := sd_of_ge T G b (not_lt.1 hbl)
        rw [hs, if_neg (by omega), List.take_of_length_le (by omega),
          List.take_of_length_le (by omega)]
  rw [key B le_rfl, List.take_of_length_le (by omega)]
  have hfin : (l.filter (· ≤ i)).toFinset = G.filter (· ≤ i) := by
    ext x
    simp [hl, and_comm]
  simp only [hfin]

end TRS.Dev.GoalUpper
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

namespace TRS.Dev.GoalUpper

lemma proj_spec {d : ℕ} (K : Set (Vector d)) (hne : K.Nonempty) (hc : IsClosed K)
    (hv : Convex ℝ K) (x : Vector d) :
    convexProjection K x ∈ K ∧
      ∀ w ∈ K, inner ℝ (x - convexProjection K x) (w - convexProjection K x) ≤ 0 := by
  have hh : K.Nonempty ∧ IsClosed K ∧ Convex ℝ K := ⟨hne, hc, hv⟩
  have hdef : convexProjection K x =
      Classical.choose (exists_norm_eq_iInf_of_complete_convex hh.1 hh.2.1.isComplete hh.2.2 x) := by
    unfold convexProjection
    rw [dif_pos hh]
  obtain ⟨hmem, heq⟩ :=
    Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hh.1 hh.2.1.isComplete hh.2.2 x)
  rw [hdef]
  refine ⟨hmem, ?_⟩
  exact (norm_eq_iInf_iff_real_inner_le_zero hv hmem).1 heq

lemma proj_lipschitz {d : ℕ} (K : Set (Vector d)) (hne : K.Nonempty) (hc : IsClosed K)
    (hv : Convex ℝ K) : LipschitzWith 1 (convexProjection K) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨hp, hpi⟩ := proj_spec K hne hc hv x
  obtain ⟨hq, hqi⟩ := proj_spec K hne hc hv y
  set p := convexProjection K x
  set q := convexProjection K y
  have h1 := hpi q hq
  have h2 := hqi p hp
  have h3 : ‖p - q‖ ^ 2 ≤ inner ℝ (x - y) (p - q) := by
    have e1 : inner ℝ (x - p) (q - p) = -inner ℝ (x - p) (p - q) := by
      rw [← inner_neg_right, neg_sub]
    have e2 : inner ℝ (x - p - (y - q)) (p - q) =
        inner ℝ (x - p) (p - q) - inner ℝ (y - q) (p - q) := inner_sub_left _ _ _
    have e3 : inner ℝ (x - y) (p - q) = inner ℝ (x - p - (y - q)) (p - q) +
        inner ℝ (p - q) (p - q) := by
      rw [← inner_add_left]; congr 1; abel
    rw [real_inner_self_eq_norm_sq] at e3
    linarith
  have h4 : inner ℝ (x - y) (p - q) ≤ ‖x - y‖ * ‖p - q‖ := real_inner_le_norm _ _
  rw [dist_eq_norm, dist_eq_norm]
  simp only [NNReal.coe_one, one_mul]
  by_cases h0 : ‖p - q‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖p - q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

lemma proj_ball_measurable {d : ℕ} (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    Measurable (convexProjection (Metric.closedBall (0 : Vector d) Δ)) :=
  (proj_lipschitz _ ⟨0, Metric.mem_closedBall_self hΔ⟩ Metric.isClosed_closedBall
    (convex_closedBall _ _)).continuous.measurable

lemma anchoredAverage_continuous {T d : ℕ} (θ₀ : Vector d) (I : Finset (Fin T)) :
    Continuous (fun h : Data T d => anchoredAverage θ₀ I h) := by
  unfold anchoredAverage crossMoment
  have hs : Continuous (fun h : Data T d => ∑ i ∈ I,
      ((h i).2 - inner ℝ (h i).1 θ₀) • (h i).1) := by
    apply continuous_finset_sum
    intro i _
    have h1 : Continuous (fun h : Data T d => (h i).1) := (continuous_apply i).fst
    have h2 : Continuous (fun h : Data T d => (h i).2) := (continuous_apply i).snd
    exact (h2.sub (Continuous.inner h1 continuous_const)).smul h1
  exact hs.const_smul (I.card : ℝ)⁻¹

lemma obs_continuous {T d : ℕ} (θ : Fin T → Vector d) :
    Continuous (fun z : GaussianRows T d => observations θ z) := by
  unfold observations
  apply continuous_pi
  intro i
  have h1 : Continuous (fun z : GaussianRows T d => (z i).1) := (continuous_apply i).fst
  have h2 : Continuous (fun z : GaussianRows T d => (z i).2) := (continuous_apply i).snd
  exact h1.prodMk ((Continuous.inner h1 continuous_const).add h2)

noncomputable def headFn (T d : ℕ) (θ₀ : Vector d) (Δ : ℝ) (n : ℕ) (h : Data T d) : Vector d :=
  if n = 0 ∨ T ≤ n then θ₀ else
    θ₀ + convexProjection (Metric.closedBall (0 : Vector d) Δ)
      (anchoredAverage θ₀ (Finset.univ.filter (fun i : Fin T => i.val < n)) h)

lemma headFn_measurable (T d : ℕ) (θ₀ : Vector d) (Δ : ℝ) (hΔ : 0 ≤ Δ) (n : ℕ) :
    Measurable (headFn T d θ₀ Δ n) := by
  unfold headFn
  by_cases h : n = 0 ∨ T ≤ n
  · simp only [h, if_true]; exact measurable_const
  · simp only [h, if_false]
    exact measurable_const.add ((proj_ball_measurable Δ hΔ).comp
      (anchoredAverage_continuous θ₀ _).measurable)

lemma geometricCount_le (T d B : ℕ) (Δ : ℝ) : geometricCount T d B Δ ≤ B := by
  unfold geometricCount
  simp only []
  split_ifs with h1 h2
  · exact Nat.zero_le _
  · exact le_rfl
  · have : Real.log (effectiveHorizon T d Δ) ≤ ((B + 1 : ℕ) : ℝ) := by
      push_cast; exact not_lt.1 h2
    have := Nat.ceil_le.2 this
    omega

lemma grid_lt (T d B : ℕ) (Δ : ℝ) : ∀ n ∈ geometricGrid T d B Δ, n < T := by
  intro n hn
  rw [grid_eq] at hn
  exact (Finset.mem_filter.1 hn).2

lemma grid_pos (T d B : ℕ) (hd : 0 < d) (hT : 0 < T) (Δ : ℝ) (hΔ : 0 < Δ) :
    ∀ n ∈ geometricGrid T d B Δ, 1 ≤ n := by
  intro n hn
  rw [grid_eq] at hn
  obtain ⟨hn1, _⟩ := Finset.mem_filter.1 hn
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hn1
  have hm0 : 0 < effectiveHorizon T d Δ := by unfold effectiveHorizon; positivity
  have : 0 < ((d : ℝ) / Δ ^ 2) *
      (effectiveHorizon T d Δ ^ (1 / ((geometricCount T d B Δ : ℕ) + 1 : ℝ))) ^ j := by
    have := Real.rpow_pos_of_pos hm0 (1 / ((geometricCount T d B Δ : ℕ) + 1 : ℝ))
    positivity
  exact Nat.ceil_pos.2 this

lemma grid_card (T d B : ℕ) (Δ : ℝ) : (geometricGrid T d B Δ).card ≤ B := by
  rw [grid_eq]
  calc _ ≤ ((Finset.Icc 1 (geometricCount T d B Δ)).image _).card := Finset.card_filter_le _ _
    _ ≤ (Finset.Icc 1 (geometricCount T d B Δ)).card := Finset.card_image_le
    _ ≤ B := by
      rw [Nat.card_Icc]
      have := geometricCount_le T d B Δ
      omega

lemma deployed_eq (T d B : ℕ) (θ₀ : Vector d) (Δ : ℝ)
    (ω : Transcript unitSeed T d) (i : Fin T) :
    deployed θ₀ (geometricPolicy T d B θ₀ Δ) ω i =
      if h : ((geometricGrid T d B Δ).filter (· ≤ i.val)).Nonempty then
        headFn T d θ₀ Δ (((geometricGrid T d B Δ).filter (· ≤ i.val)).max' h) ω.2 else θ₀ :=
  fold_char T B (geometricGrid T d B Δ) (grid_lt T d B Δ) (grid_card T d B Δ) θ₀
    (fun n => headFn T d θ₀ Δ n ω.2) i.val i.isLt

end TRS.Dev.GoalUpper
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

namespace TRS.Dev.GoalUpper

instance gaussianRows_prob (T d : ℕ) : IsProbabilityMeasure (gaussianRows T d) := by
  unfold gaussianRows
  infer_instance

lemma isCausal_geometric (T d B : ℕ) (θ₀ : Vector d) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    IsCausal (geometricPolicy T d B θ₀ Δ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j ω
    exact sd_le T _ (grid_lt T d B Δ) j.val
  · intro ω a b hab
    exact sd_mono T _ (grid_lt T d B Δ) hab
  · intro j n
    show @MeasurableSet _ (information unitSeed T d n)
      {ω : Transcript unitSeed T d | geometricDate T d B Δ j ≤ n}
    by_cases h : geometricDate T d B Δ j ≤ n
    · simp only [h, Set.setOf_true]; exact @MeasurableSet.univ _ (information unitSeed T d n)
    · simp only [h, Set.setOf_false]; exact @MeasurableSet.empty _ (information unitSeed T d n)
  · intro j n
    show @Measurable _ _ (information unitSeed T d n) _
      (fun ω : Transcript unitSeed T d => if geometricDate T d B Δ j ≤ n then
        headFn T d θ₀ Δ (geometricDate T d B Δ j) ω.2 else 0)
    by_cases h : geometricDate T d B Δ j ≤ n
    · simp only [h, if_true]
      have hΨ : @Measurable _ _ (information unitSeed T d n) inferInstance
          (fun ω : Transcript unitSeed T d =>
            (ω.1, fun i : Fin T => if i.val < n then ω.2 i else ((0 : Vector d), (0 : ℝ)))) :=
        comap_measurable _
      have hg : Measurable (fun ω' : Transcript unitSeed T d =>
          headFn T d θ₀ Δ (geometricDate T d B Δ j) ω'.2) :=
        (headFn_measurable T d θ₀ Δ hΔ _).comp measurable_snd
      have e : (fun ω : Transcript unitSeed T d => headFn T d θ₀ Δ (geometricDate T d B Δ j) ω.2) =
          (fun ω' : Transcript unitSeed T d => headFn T d θ₀ Δ (geometricDate T d B Δ j) ω'.2) ∘
          (fun ω : Transcript unitSeed T d =>
            (ω.1, fun i : Fin T => if i.val < n then ω.2 i else ((0 : Vector d), (0 : ℝ)))) := by
        funext ω
        simp only [Function.comp]
        unfold headFn
        split_ifs with h1
        · rfl
        · congr 2
          unfold anchoredAverage
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          have : i.val < geometricDate T d B Δ j := (Finset.mem_filter.1 hi).2
          show crossMoment θ₀ (ω.2 i) = crossMoment θ₀ (if i.val < n then ω.2 i else (0, 0))
          rw [if_pos (lt_of_lt_of_le this h)]
      rw [e]
      exact hg.comp hΨ
    · simp only [h, if_false]
      exact measurable_const

lemma round_bound (T d : ℕ) (hT : 0 < T) (hd : 0 < d) (θ₀ : Vector d) (Δ : ℝ)
    (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) (θ : Vector d) (hθ : ‖θ - θ₀‖ ≤ Δ) (n : ℕ)
    (hn1 : 1 ≤ n) (hnT : n < T) :
    ∫⁻ z, ENNReal.ofReal
        (‖headFn T d θ₀ Δ n (observations (fun _ : Fin T => θ) z) - θ‖ ^ 2)
      ∂(gaussianRows T d) ≤ ENNReal.ofReal ((2 * (d : ℝ) + 1) / n) := by
  have hβ : ∀ i : Fin T, ‖(fun _ : Fin T => θ) i - θ₀‖ ≤ 1 := fun i => hθ.trans hΔ1
  have h2 := (anchored_cross_moments T d hT hd θ₀ (fun _ => θ) hβ).2
  set I : Finset (Fin T) := Finset.univ.filter (fun i : Fin T => i.val < n) with hI
  have hcard : I.card = n := by
    rw [hI, Fin.card_filter_val_lt]; omega
  have hIne : I.Nonempty := by
    rw [← Finset.card_pos, hcard]; omega
  have hpath : pathAverage (fun i : Fin T => (fun _ : Fin T => θ) i - θ₀) I = θ - θ₀ := by
    unfold pathAverage
    rw [Finset.sum_const, hcard, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      linarith), one_smul]
  have hmem : pathAverage (fun i : Fin T => (fun _ : Fin T => θ) i - θ₀) I ∈
      Metric.closedBall (0 : Vector d) Δ := by
    rw [hpath]; simpa using hθ
  have h3 := h2 I hIne _ Metric.isClosed_closedBall (convex_closedBall _ _) hmem
  have hnT' : headFn T d θ₀ Δ n = fun h =>
      θ₀ + convexProjection (Metric.closedBall (0 : Vector d) Δ) (anchoredAverage θ₀ I h) := by
    funext h
    unfold headFn
    rw [if_neg (by omega)]
  have hint : (∫⁻ z, ENNReal.ofReal
        (‖headFn T d θ₀ Δ n (observations (fun _ : Fin T => θ) z) - θ‖ ^ 2)
      ∂(gaussianRows T d)) = ∫⁻ z, ENNReal.ofReal
        (‖convexProjection (Metric.closedBall (0 : Vector d) Δ)
            (anchoredAverage θ₀ I (observations (fun _ : Fin T => θ) z)) -
          pathAverage (fun i : Fin T => (fun _ : Fin T => θ) i - θ₀) I‖ ^ 2)
      ∂(gaussianRows T d) := by
    apply lintegral_congr
    intro z
    rw [hnT', hpath]
    have e : ∀ P : Vector d, θ₀ + P - θ = P - (θ - θ₀) := fun P => by abel
    simp only [e]
  rw [hint]
  refine h3.trans (min_le_left _ _ |>.trans ?_)
  rw [hcard]

end TRS.Dev.GoalUpper
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

namespace TRS.Dev.GoalUpper

lemma lintegral_snd_prob {S X : Type*} [MeasurableSpace S] [MeasurableSpace X]
    (P : Measure S) [IsProbabilityMeasure P] (ν : Measure X) [SFinite ν]
    (F : X → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω, F ω.2 ∂(P.prod ν) = ∫⁻ x, F x ∂ν := by
  rw [lintegral_prod (fun ω : S × X => F ω.2) (hF.comp measurable_snd).aemeasurable]
  simp

lemma bnd_nonneg (G : Finset ℕ) (d : ℕ) (Δ : ℝ) (i : ℕ) : 0 ≤ bnd G d Δ i := by
  unfold bnd
  split_ifs
  · positivity
  · positivity

theorem worstRisk_le (T d B : ℕ) (hT : 0 < T) (hd : 0 < d) (θ₀ : Vector d) (Δ : ℝ)
    (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1) :
    worstRisk θ₀ Δ (geometricPolicy T d B θ₀ Δ) ≤
      ENNReal.ofReal (5 * (d : ℝ) * releaseRate B (effectiveHorizon T d Δ)) := by
  unfold worstRisk
  apply iSup_le
  rintro ⟨θ, hθ⟩
  show policyRisk θ₀ (geometricPolicy T d B θ₀ Δ) (fun _ => θ) ≤ _
  set G := geometricGrid T d B Δ with hG
  let Dfn : ℕ → Data T d → Vector d := fun i h =>
    if hh : (G.filter (· ≤ i)).Nonempty then
      headFn T d θ₀ Δ ((G.filter (· ≤ i)).max' hh) h else θ₀
  have hD : ∀ i, Measurable (Dfn i) := by
    intro i
    by_cases hh : (G.filter (· ≤ i)).Nonempty
    · simp only [Dfn, dif_pos hh]; exact headFn_measurable T d θ₀ Δ hΔ.le _
    · simp only [Dfn, dif_neg hh]; exact measurable_const
  have hdep : ∀ (ω : Transcript unitSeed T d) (i : Fin T),
      deployed θ₀ (geometricPolicy T d B θ₀ Δ) (ω.1, observations (fun _ : Fin T => θ) ω.2) i =
        Dfn i.val (observations (fun _ : Fin T => θ) ω.2) :=
    fun ω i => deployed_eq T d B θ₀ Δ (ω.1, observations (fun _ : Fin T => θ) ω.2) i
  have hobs : Measurable (fun z : GaussianRows T d => observations (fun _ : Fin T => θ) z) :=
    (obs_continuous _).measurable
  set e : Fin T → GaussianRows T d → ℝ := fun i z =>
    ‖Dfn i.val (observations (fun _ : Fin T => θ) z) - θ‖ ^ 2 with he
  have he_meas : ∀ i, Measurable (e i) := by
    intro i
    exact (((hD i.val).comp hobs).sub measurable_const).norm.pow_const 2
  have h1 : policyRisk θ₀ (geometricPolicy T d B θ₀ Δ) (fun _ => θ) =
      ∫⁻ ω : unitSeed.space × GaussianRows T d,
        (fun z : GaussianRows T d => ENNReal.ofReal ((1 / 2 : ℝ) * ∑ i : Fin T, e i z)) ω.2
        ∂(unitSeed.law.prod (gaussianRows T d)) := by
    unfold policyRisk
    apply lintegral_congr
    intro ω
    simp only [hdep, he]
  have hm : Measurable (fun z : GaussianRows T d =>
      ENNReal.ofReal ((1 / 2 : ℝ) * ∑ i : Fin T, e i z)) := by
    apply Measurable.ennreal_ofReal
    exact measurable_const.mul (Finset.measurable_sum _ (fun i _ => he_meas i))
  rw [h1, lintegral_snd_prob unitSeed.law (gaussianRows T d) _ hm]
  have h2 : ∀ z, ENNReal.ofReal ((1 / 2 : ℝ) * ∑ i : Fin T, e i z) =
      ENNReal.ofReal (1 / 2) * ∑ i : Fin T, ENNReal.ofReal (e i z) := by
    intro z
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_sum_of_nonneg
      (fun i _ => by simp only [he]; positivity)]
  simp_rw [h2]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_finset_sum _ (fun i _ => (he_meas i).ennreal_ofReal)]
  -- per-round bounds
  have hround : ∀ i : Fin T, ∫⁻ z, ENNReal.ofReal (e i z) ∂(gaussianRows T d) ≤
      ENNReal.ofReal (bnd G d Δ i.val) := by
    intro i
    by_cases hh : (G.filter (· ≤ i.val)).Nonempty
    · have hmax := Finset.max'_mem _ hh
      have hmG : (G.filter (· ≤ i.val)).max' hh ∈ G := (Finset.mem_filter.1 hmax).1
      have h1' := grid_pos T d B hd hT Δ hΔ _ hmG
      have h2' := grid_lt T d B Δ _ hmG
      have := round_bound T d hT hd θ₀ Δ hΔ.le hΔ₁ θ hθ _ h1' h2'
      have hbnd : bnd G d Δ i.val =
          (2 * (d : ℝ) + 1) / (((G.filter (· ≤ i.val)).max' hh : ℕ) : ℝ) := by
        unfold bnd; rw [dif_pos hh]
      rw [hbnd]
      simp only [he, Dfn, dif_pos hh]
      exact this
    · have hbnd : bnd G d Δ i.val = Δ ^ 2 := by unfold bnd; rw [dif_neg hh]
      rw [hbnd]
      simp only [he, Dfn, dif_neg hh]
      rw [lintegral_const, measure_univ, mul_one]
      apply ENNReal.ofReal_le_ofReal
      have : ‖θ₀ - θ‖ ≤ Δ := by rw [norm_sub_rev]; exact hθ
      have h0 := norm_nonneg (θ₀ - θ)
      nlinarith
  calc ENNReal.ofReal (1 / 2) * ∑ i : Fin T, ∫⁻ z, ENNReal.ofReal (e i z) ∂(gaussianRows T d)
      ≤ ENNReal.ofReal (1 / 2) * ∑ i : Fin T, ENNReal.ofReal (bnd G d Δ i.val) :=
        by gcongr with i hi; exact hround i
    _ = ENNReal.ofReal ((1 / 2) * ∑ i : Fin T, bnd G d Δ i.val) := by
        rw [ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_sum_of_nonneg (fun i _ => bnd_nonneg _ _ _ _)]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have := grid_sum_le T d B hT hd Δ hΔ hΔ₁
        rw [Fin.sum_univ_eq_sum_range (fun i => bnd G d Δ i) T]
        linarith

end TRS.Dev.GoalUpper
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

namespace TRS.Dev.GoalUpper

lemma worstRisk_zero (T d : ℕ) (hd : 0 < d) (θ₀ : Vector d) (Δ : ℝ) (hΔ : 0 < Δ)
    {s : RandomSeed} (π : ReleasePolicy s T d 0) :
    worstRisk θ₀ Δ π = ENNReal.ofReal ((T : ℝ) * Δ ^ 2 / 2) := by
  have hrisk : ∀ θ : Vector d, policyRisk θ₀ π (fun _ => θ) =
      ENNReal.ofReal ((T : ℝ) * ‖θ₀ - θ‖ ^ 2 / 2) := by
    intro θ
    unfold policyRisk
    have hdep : ∀ (ω : Transcript s T d) (i : Fin T), deployed θ₀ π ω i = θ₀ := by
      intro ω i; simp [deployed]
    simp only [hdep]
    rw [lintegral_const, measure_univ, mul_one]
    congr 1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  unfold worstRisk
  apply le_antisymm
  · apply iSup_le
    rintro ⟨θ, hθ⟩
    show policyRisk θ₀ π (fun _ => θ) ≤ _
    rw [hrisk]
    apply ENNReal.ofReal_le_ofReal
    have : ‖θ₀ - θ‖ ≤ Δ := by rw [norm_sub_rev]; exact hθ
    have h0 := norm_nonneg (θ₀ - θ)
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    have h2 : ‖θ₀ - θ‖ ^ 2 ≤ Δ ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left h2 hT0
    linarith
  · let e : Vector d := EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ)
    have he : ‖e‖ = 1 := by simp [e]
    have hmem : ‖(θ₀ + Δ • e) - θ₀‖ ≤ Δ := by
      rw [add_sub_cancel_left, norm_smul, he, Real.norm_eq_abs, abs_of_pos hΔ]; simp
    refine le_trans ?_ (le_iSup _ ⟨θ₀ + Δ • e, hmem⟩)
    show _ ≤ policyRisk θ₀ π (fun _ => θ₀ + Δ • e)
    rw [hrisk]
    apply ENNReal.ofReal_le_ofReal
    have : ‖θ₀ - (θ₀ + Δ • e)‖ = Δ := by
      rw [sub_add_cancel_left, norm_neg, norm_smul, he, Real.norm_eq_abs, abs_of_pos hΔ]; simp
    rw [this]

theorem minimax_zero (T d : ℕ) (hd : 0 < d) (θ₀ : Vector d) (Δ : ℝ) (hΔ : 0 < Δ) :
    minimaxRisk T d 0 θ₀ Δ = ENNReal.ofReal ((T : ℝ) * Δ ^ 2 / 2) := by
  unfold TightReleaseSchedules.Stationary.minimaxRisk
  apply le_antisymm
  · apply sInf_le
    exact ⟨unitSeed, geometricPolicy T d 0 θ₀ Δ, isCausal_geometric T d 0 θ₀ Δ hΔ.le,
      (worstRisk_zero T d hd θ₀ Δ hΔ _).symm⟩
  · apply le_sInf
    rintro v ⟨s, π, _, rfl⟩
    exact (worstRisk_zero T d hd θ₀ Δ hΔ π).ge

/-- Clauses (1), (2), (3), (4), (6) of `stationary_shift_release_budget`
(everything except the lower-bound clause (5)). -/
theorem upper_parts (T d B : ℕ) (hT : 0 < T) (hd : 0 < d)
    (θ₀ : Vector d) (Δ : ℝ) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1) :
    minimaxRisk T d B θ₀ Δ ≤
      ENNReal.ofReal (5 * (d : ℝ) * releaseRate B (effectiveHorizon T d Δ)) ∧
    IsCausal (geometricPolicy T d B θ₀ Δ) ∧
    HasDeterministicDates (geometricPolicy T d B θ₀ Δ) ∧
    worstRisk θ₀ Δ (geometricPolicy T d B θ₀ Δ) ≤
      ENNReal.ofReal (5 * (d : ℝ) * releaseRate B (effectiveHorizon T d Δ)) ∧
    (B = 0 → minimaxRisk T d B θ₀ Δ = ENNReal.ofReal ((T : ℝ) * Δ ^ 2 / 2)) := by
  have hc := isCausal_geometric T d B θ₀ Δ hΔ.le
  have hw := worstRisk_le T d B hT hd θ₀ Δ hΔ hΔ₁
  refine ⟨?_, hc, fun j => ⟨geometricDate T d B Δ j, fun _ => rfl⟩, hw, ?_⟩
  · refine le_trans ?_ hw
    apply sInf_le
    exact ⟨unitSeed, geometricPolicy T d B θ₀ Δ, hc, rfl⟩
  · intro hB
    subst hB
    exact minimax_zero T d hd θ₀ Δ hΔ

end TRS.Dev.GoalUpper
end

section
/-!
PLAN (q382, Lemma 4.2). Constants: amp(l) = 2^{-5-l/2}, a = amp, rho = a sqrt|S|/16.
(1) per level ||level|| <= amp sqrt|S|; 2^{l0} >= 16|S|/Delta^2; geometric sum < Delta/32.
(2) core: change of measure.  Fix seed and the other levels (u0); the n observed rows depend on the
    level-l draw only through y_i = <x_i, theta0> + eps_i + <x_i, a u_l>.  Shear eps'_i = eps_i + <x_i,a u_l>
    (rows i<n) has density D = exp(sum eps' m_i - m_i^2/2) wrt gaussianRows.  P(success) = int D * Psi
    <= sqrt(int D^2) * sqrt(int Psi) (Cauchy-Schwarz).  int D^2 = (1-2|a u|^2)^{-n/2} <= exp(k 2^-10 * 1.001),
    int Psi <= 0.1293^k (Chernoff, lambda=128), (0.1293 * 1.0011)^{1/2} < 0.36 = 9/25.
(3) union bound over (slot, level) with estimator `if date <= n then head else 0`, n = min(T, floor 2^l);
    minimal l >= l0 with date <= 2^l, 2^l < 2 max(date, 16|S|/Delta^2).
-/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

namespace TRS.Dev.LowerErrorEventCube

instance : IsProbabilityMeasure uniformCoordinate := by
  constructor
  have hemb : MeasurableEmbedding (Subtype.val : CubeCoordinate → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  unfold uniformCoordinate
  rw [Measure.smul_apply, hemb.comap_apply]
  simp
  have : {x : ℝ | -1 ≤ x ∧ x ≤ 1} = Set.Icc (-1) 1 := rfl
  rw [this, Real.volume_Icc]
  norm_num
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ENNReal.inv_mul_cancel] <;> simp

end TRS.Dev.LowerErrorEventCube
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.LowerErrorEventLevels

end TRS.Dev.LowerErrorEventLevels

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.LowerErrorEventShear

abbrev Row (d : ℕ) := Vector d × ℝ

def rowMeasure (d : ℕ) : Measure (Row d) := (stdGaussian (Vector d)).prod (gaussianReal 0 1)

instance (d : ℕ) : IsProbabilityMeasure (rowMeasure d) := by
  unfold rowMeasure; infer_instance

end TRS.Dev.LowerErrorEventShear

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.LowerErrorEventShearPi

open TRS.Dev.LowerErrorEventShear

end TRS.Dev.LowerErrorEventShearPi

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.LowerErrorEventCore1

lemma norm_embedBlock {d : ℕ} (S : Finset (Fin d)) (v : BlockVector S) :
    ‖embedBlock S v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  set F : Fin d → ℝ := fun i => ‖(if h : i ∈ S then v ⟨i, h⟩ else 0 : ℝ)‖ ^ 2 with hF
  have h1 : ∑ i : Fin d, ‖(embedBlock S v) i‖ ^ 2 = ∑ i : Fin d, F i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [embedBlock, hF]
  have h2 : ∑ i : S, ‖v i‖ ^ 2 = ∑ i ∈ S, F i := by
    rw [← Finset.sum_coe_sort S F]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hF]
  rw [h1, h2]
  symm
  apply Finset.sum_subset (Finset.subset_univ S)
  intro i _ hi
  simp [hF, hi]

def vecOf {d : ℕ} {S : Finset (Fin d)} (v : S → CubeCoordinate) : BlockVector S :=
  WithLp.toLp 2 (fun i : S => (v i : ℝ))

lemma measurable_vecOf {d : ℕ} {S : Finset (Fin d)} : Measurable (vecOf (S := S)) := by
  unfold vecOf
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  refine measurable_pi_lambda _ fun i => ?_
  exact measurable_subtype_coe.comp (measurable_pi_apply i)

lemma measurable_hiddenShift {d : ℕ} (S : Finset (Fin d)) (Δ : ℝ) (L : ℤ) :
    Measurable (hiddenShift S Δ L) := by
  unfold hiddenShift
  refine Finset.measurable_sum _ fun ℓ _ => ?_
  have : Measurable fun u : PriorDraws S Δ L => vecOf (u ℓ) :=
    measurable_vecOf.comp (measurable_pi_apply ℓ)
  exact this.const_smul (levelAmplitude ℓ.val)

lemma measurable_embedBlock {d : ℕ} (S : Finset (Fin d)) : Measurable (embedBlock S) := by
  unfold embedBlock
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i ∈ S
  · simp only [h, dif_pos]
    exact (measurable_pi_apply (⟨i, h⟩ : S)).comp (PiLp.continuous_ofLp 2 _).measurable
  · simp [h]

lemma measurable_priorTranscript {s : RandomSeed} {T d : ℕ} {S : Finset (Fin d)} {Δ : ℝ} {L : ℤ}
    (g : Fin T → Vector d) : Measurable (priorTranscript (s := s) (S := S) (Δ := Δ) (L := L) g) := by
  unfold priorTranscript observations
  refine measurable_fst.prodMk (measurable_pi_lambda _ fun i => ?_)
  have hθ : Measurable fun ω : PriorSample s T d S Δ L =>
      g i + embedBlock S (hiddenShift S Δ L ω.2.1) :=
    measurable_const.add ((measurable_embedBlock S).comp
      ((measurable_hiddenShift S Δ L).comp (measurable_fst.comp measurable_snd)))
  have hx : Measurable fun ω : PriorSample s T d S Δ L => (ω.2.2 i).1 :=
    measurable_fst.comp ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))
  have he : Measurable fun ω : PriorSample s T d S Δ L => (ω.2.2 i).2 :=
    measurable_snd.comp ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))
  exact hx.prodMk ((hx.inner hθ).add he)

lemma priorInformation_le {s : RandomSeed} {T d : ℕ} {S : Finset (Fin d)} {Δ : ℝ} {L : ℤ}
    (g : Fin T → Vector d) (n : ℕ) :
    priorInformation (s := s) (S := S) (Δ := Δ) (L := L) g n ≤
      (inferInstance : MeasurableSpace (PriorSample s T d S Δ L)) := by
  have hF : Measurable (fun ω : Transcript s T d =>
      (ω.1, fun i : Fin T => if i.val < n then ω.2 i else (0, 0))) := by
    refine measurable_fst.prodMk (measurable_pi_lambda _ fun i => ?_)
    by_cases h : i.val < n
    · simp only [h, if_true]
      exact (measurable_pi_apply i).comp measurable_snd
    · simp [h]
  have hI : information s T d n ≤ (inferInstance : MeasurableSpace (Transcript s T d)) :=
    hF.comap_le
  calc priorInformation (s := s) (S := S) (Δ := Δ) (L := L) g n
      ≤ MeasurableSpace.comap (priorTranscript g) inferInstance :=
        MeasurableSpace.comap_mono hI
    _ ≤ _ := (measurable_priorTranscript g).comap_le

end TRS.Dev.LowerErrorEventCore1

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.LowerErrorEventCore2

end TRS.Dev.LowerErrorEventCore2

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.LowerErrorEventCore3

instance instProbU {d : ℕ} (S : Finset (Fin d)) (Δ : ℝ) (L : ℤ) :
    IsProbabilityMeasure (uniformLevels S Δ L) := by
  unfold uniformLevels; infer_instance

instance instProbG (T d : ℕ) : IsProbabilityMeasure (gaussianRows T d) := by
  unfold gaussianRows; infer_instance

open TRS.Dev.LowerErrorEventCore1 TRS.Dev.LowerErrorEventCore2 TRS.Dev.LowerErrorEventLevels

open TRS.Dev.LowerErrorEventShear TRS.Dev.LowerErrorEventShearPi

end TRS.Dev.LowerErrorEventCore3

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.GoalLower

open TRS.Dev.LowerErrorEventCore1 TRS.Dev.LowerErrorEventCore3

/-- Reshuffle `(u,(σ,z)) ↦ (σ,(u,z))`. -/
def reshuffle (α β γ : Type*) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    α × (β × γ) ≃ᵐ β × (α × γ) :=
  (MeasurableEquiv.prodAssoc.symm.trans
    ((MeasurableEquiv.prodComm (α := α) (β := β)).prodCongr (MeasurableEquiv.refl γ))).trans
    MeasurableEquiv.prodAssoc

lemma reshuffle_mp {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ρ : Measure γ) [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (reshuffle α β γ) (μ.prod (ν.prod ρ)) (ν.prod (μ.prod ρ)) := by
  unfold reshuffle
  have h1 := (measurePreserving_prodAssoc μ ν ρ).symm
  have h2 : MeasurePreserving (Prod.map Prod.swap (id : γ → γ)) ((μ.prod ν).prod ρ)
      ((ν.prod μ).prod ρ) := (Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod
        (MeasurePreserving.id ρ)
  have h3 := measurePreserving_prodAssoc ν μ ρ
  exact h3.comp (h2.comp h1)


/-- Per-sample loss of the deployed predictors under the cube prior with centre `g0`. -/
def pathLoss {s : RandomSeed} {T d B : ℕ} (θ₀ : Vector d) (π : ReleasePolicy s T d B)
    (g0 : Vector d) (Δ : ℝ) (L : ℤ) (ω : PriorSample s T d (Finset.univ : Finset (Fin d)) Δ L) :
    ℝ≥0∞ :=
  ENNReal.ofReal ((1 / 2 : ℝ) * ∑ i : Fin T,
    ‖deployed θ₀ π (priorTranscript (fun _ : Fin T => g0) ω) i -
      (g0 + embedBlock (Finset.univ : Finset (Fin d)) (hiddenShift Finset.univ Δ L ω.2.1))‖ ^ 2)

theorem prior_le_worst {s : RandomSeed} {T d B : ℕ} (θ₀ : Vector d) (Δ : ℝ)
    (π : ReleasePolicy s T d B) (g0 : Vector d) (L : ℤ)
    (hg0 : ‖g0 - θ₀‖ + Δ / 32 ≤ Δ)
    (hH : ∀ u : PriorDraws (Finset.univ : Finset (Fin d)) Δ L,
      ‖hiddenShift Finset.univ Δ L u‖ < Δ / 32) :
    ∫⁻ ω, pathLoss θ₀ π g0 Δ L ω ∂(priorLaw s T d Finset.univ Δ L) ≤ worstRisk θ₀ Δ π := by
  have hmp := reshuffle_mp (uniformLevels (Finset.univ : Finset (Fin d)) Δ L) s.law
    (gaussianRows T d)
  have h1 : ∫⁻ ω, pathLoss θ₀ π g0 Δ L ω ∂(priorLaw s T d Finset.univ Δ L) =
      ∫⁻ p, pathLoss θ₀ π g0 Δ L (reshuffle _ _ _ p) ∂((uniformLevels Finset.univ Δ L).prod
        (s.law.prod (gaussianRows T d))) := by
    have := hmp.lintegral_comp_emb (reshuffle _ _ _).measurableEmbedding
      (pathLoss θ₀ π g0 Δ L)
    unfold priorLaw
    exact this.symm
  rw [h1]
  refine (lintegral_prod_le _).trans ?_
  have h2 : ∀ u : PriorDraws (Finset.univ : Finset (Fin d)) Δ L,
      ∫⁻ y, pathLoss θ₀ π g0 Δ L (reshuffle _ _ _ (u, y)) ∂(s.law.prod (gaussianRows T d)) ≤
        worstRisk θ₀ Δ π := by
    intro u
    have hmem : ‖(g0 + embedBlock (Finset.univ : Finset (Fin d)) (hiddenShift Finset.univ Δ L u))
        - θ₀‖ ≤ Δ := by
      have : (g0 + embedBlock (Finset.univ : Finset (Fin d)) (hiddenShift Finset.univ Δ L u))
          - θ₀ = (g0 - θ₀) + embedBlock Finset.univ (hiddenShift Finset.univ Δ L u) := by abel
      rw [this]
      refine (norm_add_le _ _).trans ?_
      rw [norm_embedBlock]
      linarith [hH u]
    refine le_trans (le_of_eq ?_) (le_iSup _ ⟨_, hmem⟩)
    unfold policyRisk pathLoss
    rfl
  calc ∫⁻ x, ∫⁻ y, pathLoss θ₀ π g0 Δ L (reshuffle _ _ _ (x, y)) ∂(s.law.prod (gaussianRows T d))
        ∂(uniformLevels Finset.univ Δ L) ≤ ∫⁻ x, worstRisk θ₀ Δ π ∂(uniformLevels Finset.univ Δ L) :=
        lintegral_mono h2
    _ = worstRisk θ₀ Δ π := by simp

end TRS.Dev.GoalLower
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.GoalLower

lemma foldl_spec {α β : Type*} (c : β → Prop) [DecidablePred c] (h : β → α) (w : α) (l : List β) :
    (List.foldl (fun r j => if c j then h j else r) w l = w ∧ ∀ k ∈ l, ¬ c k) ∨
    ∃ j, c j ∧ List.foldl (fun r j => if c j then h j else r) w l = h j ∧
      ∃ l₁ l₂, l = l₁ ++ j :: l₂ ∧ ∀ k ∈ l₂, ¬ c k := by
  induction l generalizing w with
  | nil => left; simp
  | cons a l ih =>
    simp only [List.foldl_cons]
    rcases ih (if c a then h a else w) with ⟨h1, h2⟩ | ⟨j, hj, hr, l₁, l₂, hl, hl₂⟩
    · by_cases ha : c a
      · right
        refine ⟨a, ha, ?_, [], l, rfl, h2⟩
        rw [h1]; simp [ha]
      · left
        refine ⟨?_, ?_⟩
        · rw [h1]; simp [ha]
        · intro k hk
          rcases List.mem_cons.1 hk with rfl | hk
          · exact ha
          · exact h2 k hk
    · right
      exact ⟨j, hj, hr, a :: l₁, l₂, by simp [hl], hl₂⟩

/-- The deployed predictor is `θ₀` or the head of the last slot with date `≤ i`. -/
lemma deployed_spec {s : RandomSeed} {T d B : ℕ} (θ₀ : Vector d) (π : ReleasePolicy s T d B)
    (ω : Transcript s T d) (i : Fin T) :
    (deployed θ₀ π ω i = θ₀ ∧ ∀ j : Fin B, i.val < π.date j ω) ∨
    ∃ j : Fin B, π.date j ω ≤ i.val ∧ deployed θ₀ π ω i = π.head j ω ∧
      ∀ k : Fin B, j < k → i.val < π.date k ω := by
  unfold deployed
  rcases foldl_spec (fun j : Fin B => π.date j ω ≤ i.val) (fun j => π.head j ω) θ₀
    (List.finRange B) with ⟨h1, h2⟩ | ⟨j, hj, hr, l₁, l₂, hl, hl₂⟩
  · left
    refine ⟨h1, fun j => ?_⟩
    have := h2 j (List.mem_finRange j)
    omega
  · right
    refine ⟨j, hj, hr, fun k hk => ?_⟩
    have hp := List.pairwise_lt_finRange B
    rw [hl] at hp
    have hkmem : k ∈ l₁ ++ j :: l₂ := hl ▸ List.mem_finRange k
    rcases List.mem_append.1 hkmem with hk1 | hk2
    · have := (List.pairwise_append.1 hp).2.2 k hk1 j (List.mem_cons_self)
      exact absurd (lt_trans this hk) (lt_irrefl _)
    · rcases List.mem_cons.1 hk2 with rfl | hk3
      · exact absurd hk (lt_irrefl _)
      · have := hl₂ k hk3
        omega

lemma measurable_deployed {s : RandomSeed} {T d B : ℕ} (θ₀ : Vector d) (π : ReleasePolicy s T d B)
    (hπ : IsCausal π) (n : ℕ) :
    @Measurable _ _ (information s T d n) inferInstance
      (fun ω => List.foldl (fun w j => if π.date j ω ≤ n then π.head j ω else w) θ₀
        (List.finRange B)) := by
  have key : ∀ l : List (Fin B), @Measurable _ _ (information s T d n) inferInstance
      (fun ω => List.foldl (fun w j => if π.date j ω ≤ n then π.head j ω else w) θ₀ l) := by
    intro l
    induction l using List.reverseRecOn with
    | nil => exact @measurable_const _ _ _ (information s T d n) _
    | append_singleton l a ih =>
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have h3 := hπ.2.2.2 a n
      have h2 := hπ.2.2.1 a n
      have h4 : @Measurable _ _ (information s T d n) inferInstance
          (fun ω => if π.date a ω ≤ n then π.head a ω else (0 : Vector d)) := h3
      letI : MeasurableSpace (Transcript s T d) := information s T d n
      have h5 : Measurable (fun ω => if π.date a ω ≤ n then
          (if π.date a ω ≤ n then π.head a ω else (0 : Vector d))
          else List.foldl (fun w j => if π.date j ω ≤ n then π.head j ω else w) θ₀ l) :=
        Measurable.ite h2 h4 ih
      convert h5 using 2 with ω
      by_cases hc : π.date a ω ≤ n <;> simp [hc]
  exact key _

end TRS.Dev.GoalLower
end
end

section
set_option autoImplicit false
open scoped BigOperators

noncomputable section

namespace TRS.Dev.GoalLower

lemma prod_ratio (y : ℕ → ℝ) (hy : ∀ j, 0 < y j) (k : ℕ) :
    ∏ j ∈ Finset.range k, (y (j + 1) / y j) = y k / y 0 := by
  induction k with
  | zero => simp [(hy 0).ne']
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    have := (hy n).ne'
    have := (hy 0).ne'
    field_simp

lemma amgm_phases (k : ℕ) (hk : 0 < k) (y : ℕ → ℝ) (hy : ∀ j, 0 < y j) :
    (k : ℝ) * ((y k / y 0) ^ (1 / (k : ℝ)) - 1) ≤
      ∑ j ∈ Finset.range k, (y (j + 1) - y j) / y j := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h := Real.geom_mean_le_arith_mean (Finset.range k) (fun _ => (1 : ℝ))
    (fun j => y (j + 1) / y j) (fun _ _ => zero_le_one) (by simpa using hk')
    (fun j _ => (div_pos (hy _) (hy _)).le)
  simp only [Real.rpow_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    one_mul] at h
  rw [prod_ratio y hy k, one_div] at *
  have h2 : (∑ j ∈ Finset.range k, (y (j + 1) - y j) / y j) =
      ∑ j ∈ Finset.range k, (y (j + 1) / y j) - k := by
    have : ∀ j ∈ Finset.range k, (y (j + 1) - y j) / y j = y (j + 1) / y j - 1 := by
      intro j _
      have := (hy j).ne'
      field_simp
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib]
    simp
  rw [h2]
  rw [le_div_iff₀ hk'] at h
  have : (k : ℝ) * (y k / y 0) ^ (k : ℝ)⁻¹ ≤ ∑ j ∈ Finset.range k, y (j + 1) / y j := by
    linarith
  linarith


def ext (T B : ℕ) (τ : Fin B → ℕ) (n : ℕ) : ℕ := if h : n < B then τ ⟨n, h⟩ else T

def tt (T B : ℕ) (τ : Fin B → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => ext T B τ j

lemma tt_mono (T B : ℕ) (τ : Fin B → ℕ) (hmono : Monotone τ) (hτT : ∀ j, τ j ≤ T) :
    Monotone (tt T B τ) := by
  have hext : Monotone (ext T B τ) := by
    intro a b hab
    unfold ext
    by_cases hb : b < B
    · have ha : a < B := lt_of_le_of_lt hab hb
      simp only [ha, hb, dif_pos]
      exact hmono hab
    · by_cases ha : a < B
      · simp only [ha, hb, dif_pos, dif_neg, not_false_eq_true]; exact hτT _
      · simp [ha, hb]
  intro a b hab
  cases a with
  | zero => simp [tt]
  | succ a =>
    cases b with
    | zero => omega
    | succ b => exact hext (by omega)

lemma sum_Ico_phases (t : ℕ → ℕ) (ht : Monotone t) (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.Ico (t 0) (t n), f i =
      ∑ j ∈ Finset.range n, ∑ i ∈ Finset.Ico (t j) (t (j + 1)), f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact (Finset.sum_Ico_consecutive f (ht (Nat.zero_le n)) (ht (Nat.le_succ n))).symm


lemma phase_sum (T B : ℕ) (x0 : ℝ) (hx0 : 0 < x0) (hxT : x0 ≤ T) (τ : Fin B → ℕ)
    (hmono : Monotone τ) (hτT : ∀ j, τ j ≤ T) (w : Fin T → ℝ)
    (hw : ∀ i : Fin T, ((∀ j, i.val < τ j) ∧ 1 / x0 ≤ w i) ∨
      (∃ j, τ j ≤ i.val ∧ (∀ k, j < k → i.val < τ k) ∧ 1 / max (τ j : ℝ) x0 ≤ w i)) :
    ((B : ℝ) + 1) * (((T : ℝ) / x0) ^ (1 / ((B : ℝ) + 1)) - 1) ≤ ∑ i, w i := by
  set t := tt T B τ with ht_def
  have htm : Monotone t := tt_mono T B τ hmono hτT
  have ht0 : t 0 = 0 := rfl
  have htB : t (B + 1) = T := by simp [ht_def, tt, ext]
  have htle : ∀ j, t j ≤ T := fun j => by
    rw [← htB]; rcases le_total j (B + 1) with h | h
    · exact htm h
    · have : t j = T := by
        cases j with
        | zero => omega
        | succ j => simp [ht_def, tt, ext]; intro h'; omega
      omega
  set y : ℕ → ℝ := fun j => max (t j : ℝ) x0 with hy_def
  have hy : ∀ j, 0 < y j := fun j => lt_max_of_lt_right hx0
  have hy0 : y 0 = x0 := by simp [hy_def, ht0, hx0.le]
  have hyB : y (B + 1) = T := by simp [hy_def, htB, hxT]
  let w' : ℕ → ℝ := fun n => if h : n < T then w ⟨n, h⟩ else 0
  have hsum : ∑ i, w i = ∑ i ∈ Finset.range T, w' i := by
    rw [← Fin.sum_univ_eq_sum_range (fun n => w' n) T]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [w']
  have hphase := sum_Ico_phases t htm w' (B + 1)
  rw [ht0, htB] at hphase
  have hclaim : ∀ j ∈ Finset.range (B + 1), ∀ i ∈ Finset.Ico (t j) (t (j + 1)),
      1 / y j ≤ w' i := by
    intro j hj i hi
    rw [Finset.mem_range] at hj
    rw [Finset.mem_Ico] at hi
    have hiT : i < T := lt_of_lt_of_le hi.2 (htle _)
    simp only [w', dif_pos hiT]
    rcases hw ⟨i, hiT⟩ with ⟨h1, h2⟩ | ⟨j', hj1, hj2, hj3⟩
    on_goal 1 => dsimp only at h1
    on_goal 2 => dsimp only at hj1 hj2 hj3
    · have : j = 0 := by
        by_contra hne
        obtain ⟨j₁, rfl⟩ : ∃ j₁, j = j₁ + 1 := ⟨j - 1, by omega⟩
        have : t (j₁ + 1) = τ ⟨j₁, by omega⟩ := by simp [ht_def, tt, ext, show j₁ < B by omega]
        have h3 : i < τ ⟨j₁, by omega⟩ := h1 ⟨j₁, by omega⟩
        have h4 := hi.1
        omega
      subst this
      simpa [hy0] using h2
    · have hjj : j = j' + 1 := by
        have hjB := j'.2
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have h1 : t (j + 1) ≤ t (j' + 1) := htm (by omega)
          have h2 : t (j' + 1) = τ j' := by simp [ht_def, tt, ext, hjB]
          have := hi.2
          omega
        · obtain ⟨j₁, rfl⟩ : ∃ j₁, j = j₁ + 1 := ⟨j - 1, by omega⟩
          have h2 : t (j₁ + 1) = τ ⟨j₁, by omega⟩ := by
            simp [ht_def, tt, ext, show j₁ < B by omega]
          have h3 : i < τ ⟨j₁, by omega⟩ := hj2 ⟨j₁, by omega⟩ (by rw [Fin.lt_def]; simp; omega)
          have h4 := hi.1
          omega
      subst hjj
      have h2 : t (j' + 1) = τ j' := by simp [ht_def, tt, ext, j'.2]
      have : y (j' + 1) = max (τ j' : ℝ) x0 := by simp [hy_def, h2]
      rw [this]; exact hj3
  have hbound : ∀ j ∈ Finset.range (B + 1),
      (y (j + 1) - y j) / y j ≤ ∑ i ∈ Finset.Ico (t j) (t (j + 1)), w' i := by
    intro j hj
    have hcard : ∑ i ∈ Finset.Ico (t j) (t (j + 1)), (1 / y j) =
        ((t (j + 1) : ℝ) - t j) / y j := by
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (htm (Nat.le_succ j))]
      ring
    have h1 : ∑ i ∈ Finset.Ico (t j) (t (j + 1)), (1 / y j) ≤
        ∑ i ∈ Finset.Ico (t j) (t (j + 1)), w' i :=
      Finset.sum_le_sum fun i hi => hclaim j hj i hi
    refine le_trans ?_ (hcard ▸ h1)
    apply div_le_div_of_nonneg_right _ (hy j).le
    have : (t j : ℝ) ≤ t (j + 1) := by exact_mod_cast htm (Nat.le_succ j)
    simp only [hy_def]
    simp only [max_def]
    split_ifs <;> linarith
  have hk : 0 < B + 1 := Nat.succ_pos B
  have hA := amgm_phases (B + 1) hk y hy
  rw [hy0, hyB] at hA
  rw [hsum, Finset.range_eq_Ico, hphase]
  calc _ ≤ ∑ j ∈ Finset.range (B + 1), (y (j + 1) - y j) / y j := by exact_mod_cast hA
    _ ≤ ∑ j ∈ Finset.range (B + 1), ∑ i ∈ Finset.Ico (t j) (t (j + 1)), w' i :=
      Finset.sum_le_sum hbound

end TRS.Dev.GoalLower
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.GoalLower

open TRS.Dev.LowerErrorEventCore1 TRS.Dev.LowerErrorEventCore3

lemma le_zpow_ceil (x : ℝ) (hx : 0 < x) : x ≤ (2 : ℝ) ^ ⌈Real.logb 2 x⌉ := by
  have h1 : x = (2 : ℝ) ^ (Real.logb 2 x) := (Real.rpow_logb (by norm_num) (by norm_num) hx).symm
  have h2 : (2 : ℝ) ^ (Real.logb 2 x) ≤ (2 : ℝ) ^ ((⌈Real.logb 2 x⌉ : ℤ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (Int.le_ceil _)
  rw [Real.rpow_intCast] at h2
  linarith

lemma zpow_ceil_le (x : ℝ) (hx : 0 < x) : (2 : ℝ) ^ ⌈Real.logb 2 x⌉ ≤ 2 * x := by
  have h1 : x = (2 : ℝ) ^ (Real.logb 2 x) := (Real.rpow_logb (by norm_num) (by norm_num) hx).symm
  have h2 : (2 : ℝ) ^ ((⌈Real.logb 2 x⌉ : ℤ) : ℝ) ≤ (2 : ℝ) ^ (Real.logb 2 x + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [Int.ceil_lt_add_one (Real.logb 2 x)])
  rw [Real.rpow_intCast, Real.rpow_add (by norm_num), Real.rpow_one, ← h1] at h2
  linarith

lemma ceil_le_of_le_zpow (x : ℝ) (hx : 0 < x) (L : ℤ) (h : x ≤ (2 : ℝ) ^ L) :
    ⌈Real.logb 2 x⌉ ≤ L := by
  apply Int.ceil_le.2
  rw [Real.logb_le_iff_le_rpow (by norm_num) hx, Real.rpow_intCast]
  exact h

/-- Level choice for a given sample size `n`. -/
lemma level_choice (x0 : ℝ) (hx0 : 0 < x0) (n : ℕ) (L : ℤ) (hL : ⌈Real.logb 2 x0⌉ ≤ L)
    (hnL : (n : ℝ) ≤ (2 : ℝ) ^ L) :
    ∃ ℓ : ℤ, ⌈Real.logb 2 x0⌉ ≤ ℓ ∧ ℓ ≤ L ∧ (n : ℝ) ≤ (2 : ℝ) ^ ℓ ∧
      (2 : ℝ) ^ ℓ ≤ 2 * max (n : ℝ) x0 := by
  have hx : 0 < max (n : ℝ) x0 := lt_max_of_lt_right hx0
  refine ⟨⌈Real.logb 2 (max (n : ℝ) x0)⌉, ?_, ?_, ?_, zpow_ceil_le _ hx⟩
  · exact Int.ceil_mono (Real.logb_le_logb_of_le (by norm_num) hx0 (le_max_right _ _))
  · apply ceil_le_of_le_zpow _ hx
    refine max_le hnL ?_
    have := le_zpow_ceil x0 hx0
    have h2 : (2 : ℝ) ^ ⌈Real.logb 2 x0⌉ ≤ (2 : ℝ) ^ L := zpow_le_zpow_right₀ (by norm_num) hL
    linarith
  · exact le_trans (le_max_left _ _) (le_zpow_ceil _ hx)

lemma blockProj_embed_univ {d : ℕ} (h : BlockVector (Finset.univ : Finset (Fin d))) :
    blockProjection Finset.univ (embedBlock Finset.univ h) = h := by
  ext i
  simp [blockProjection, embedBlock]

lemma blockProj_sub {d : ℕ} (S : Finset (Fin d)) (v w : Vector d) :
    blockProjection S (v - w) = blockProjection S v - blockProjection S w := by
  ext i; simp [blockProjection]

lemma norm_blockProj_univ {d : ℕ} (v : Vector d) :
    ‖blockProjection (Finset.univ : Finset (Fin d)) v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [blockProjection]
  exact Finset.sum_coe_sort (Finset.univ : Finset (Fin d)) (fun i => ‖v i‖ ^ 2)


lemma blockProj_add {d : ℕ} (S : Finset (Fin d)) (v w : Vector d) :
    blockProjection S (v + w) = blockProjection S v + blockProjection S w := by
  ext i; simp [blockProjection]

lemma err_eq {d : ℕ} (v g : Vector d) (h : BlockVector (Finset.univ : Finset (Fin d))) :
    ‖v - (g + embedBlock Finset.univ h)‖ =
      ‖blockProjection Finset.univ v - blockProjection Finset.univ g - h‖ := by
  rw [← norm_blockProj_univ, blockProj_sub, blockProj_add, blockProj_embed_univ]
  congr 1; abel

lemma measurable_blockProjection {d : ℕ} (S : Finset (Fin d)) : Measurable (blockProjection S) := by
  unfold blockProjection
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  refine measurable_pi_lambda _ fun i => ?_
  exact (measurable_pi_apply i.val).comp (PiLp.continuous_ofLp 2 _).measurable

lemma rho_le (d : ℕ) (hd : 0 < d) (M P : ℝ) (hM : 0 < M) (hP : 0 < P) (hPM : P ≤ 2 * M) :
    (2 : ℝ) ^ (-19 : ℤ) * d / M ≤ (1 / 256) * ((2 : ℝ) ^ (-10 : ℤ) * P⁻¹) * d := by
  have hd' : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : (1 : ℝ) / (2 * M) ≤ 1 / P := one_div_le_one_div_of_le hP hPM
  have e1 : (2 : ℝ) ^ (-19 : ℤ) = 1 / 524288 := by norm_num
  have e2 : (2 : ℝ) ^ (-10 : ℤ) = 1 / 1024 := by norm_num
  rw [e1, e2]
  have : (1 : ℝ) / 524288 * d / M = (1 / 262144) * (1 / (2 * M)) * d := by field_simp; ring
  rw [this]
  have : (1 / 256 : ℝ) * (1 / 1024 * P⁻¹) * d = (1 / 262144) * (1 / P) * d := by
    rw [one_div P]; ring
  rw [this]
  gcongr

lemma sum_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {ι : Type*}
    (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    ∑ i ∈ s, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑ i ∈ s, f i a ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    simp only [Finset.sum_insert ha]
    calc ∫⁻ a_1, f a a_1 ∂μ + ∑ x ∈ s, ∫⁻ a_1, f x a_1 ∂μ
        ≤ ∫⁻ a_1, f a a_1 ∂μ + ∫⁻ a_1, ∑ i ∈ s, f i a_1 ∂μ := by gcongr
      _ ≤ _ := le_lintegral_add _ _

def e0 {d : ℕ} (hd : 0 < d) : Vector d := EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ)

lemma norm_e0 {d : ℕ} (hd : 0 < d) : ‖e0 hd‖ = 1 := by simp [e0]

def g0 {d : ℕ} (hd : 0 < d) (θ₀ : Vector d) (Δ : ℝ) : Vector d := θ₀ + (Δ / 2) • e0 hd

def Lv (T d : ℕ) (Δ : ℝ) : ℤ :=
  max (firstLevel (Finset.univ : Finset (Fin d)).card Δ) ⌈Real.logb 2 (T : ℝ)⌉

lemma firstLevel_univ (d : ℕ) (Δ : ℝ) :
    firstLevel (Finset.univ : Finset (Fin d)).card Δ = ⌈Real.logb 2 (16 * (d : ℝ) / Δ ^ 2)⌉ := by
  simp [firstLevel, logTwo, Real.logb]

lemma norm_g0 {d : ℕ} (hd : 0 < d) (θ₀ : Vector d) (Δ : ℝ) (hΔ : 0 < Δ) :
    ‖g0 hd θ₀ Δ - θ₀‖ = Δ / 2 := by
  unfold g0
  rw [add_sub_cancel_left, norm_smul, norm_e0, Real.norm_eq_abs, abs_of_pos (by positivity)]
  ring

theorem round_lower {s : RandomSeed} {T d B : ℕ} (hT : 0 < T) (hd : 0 < d) (θ₀ : Vector d)
    (Δ : ℝ) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1) (π : ReleasePolicy s T d B) (hπ : IsCausal π) :
    ENNReal.ofReal ((8 / 25 : ℝ) * (2 : ℝ) ^ (-19 : ℤ) * d *
      ∑ i : Fin T, 1 / max (i.val : ℝ) (16 * (d : ℝ) / Δ ^ 2)) ≤ worstRisk θ₀ Δ π := by
  classical
  set S : Finset (Fin d) := Finset.univ with hSdef
  have hcard : S.card = d := by simp [S]
  have hS : 0 < S.card := by omega
  set x0 : ℝ := 16 * (d : ℝ) / Δ ^ 2 with hx0def
  have hx0 : 0 < x0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  set L := Lv T d Δ with hLdef
  have hL : firstLevel S.card Δ ≤ L := le_max_left _ _
  have hLT : (T : ℝ) ≤ (2 : ℝ) ^ L :=
    le_trans (le_zpow_ceil T (by exact_mod_cast hT))
      (zpow_le_zpow_right₀ (by norm_num) (le_max_right _ _))
  have hfl : firstLevel S.card Δ = ⌈Real.logb 2 x0⌉ := firstLevel_univ d Δ
  have key := common_lower_error_event T d hT hd S hS Δ hΔ hΔ₁ L hL hLT
    (fun _ => g0 hd θ₀ Δ) (blockProjection S (g0 hd θ₀ Δ)) (fun _ => rfl) s
  obtain ⟨hH, hb, -⟩ := key
  have hg0 : ‖g0 hd θ₀ Δ - θ₀‖ + Δ / 32 ≤ Δ := by rw [norm_g0 hd θ₀ Δ hΔ]; linarith
  refine le_trans ?_ (prior_le_worst θ₀ Δ π (g0 hd θ₀ Δ) L hg0 hH)
  have hnL : ∀ i : Fin T, (i.val : ℝ) ≤ (2 : ℝ) ^ L := fun i =>
    le_trans (by exact_mod_cast i.2.le) hLT
  haveI hprob : IsProbabilityMeasure (priorLaw s T d S Δ L) := by unfold priorLaw; infer_instance
  have hround : ∀ i : Fin T, ENNReal.ofReal ((8 / 25 : ℝ) *
      ((2 : ℝ) ^ (-19 : ℤ) * d / max (i.val : ℝ) x0)) ≤
      ∫⁻ ω, ENNReal.ofReal ((1 / 2 : ℝ) * ‖deployed θ₀ π
        (priorTranscript (fun _ : Fin T => g0 hd θ₀ Δ) ω) i -
          (g0 hd θ₀ Δ + embedBlock S (hiddenShift S Δ L ω.2.1))‖ ^ 2)
        ∂(priorLaw s T d S Δ L) := by
    intro i
    obtain ⟨ℓ, hℓ0, hℓL, hnℓ, hℓ2⟩ :=
      level_choice x0 hx0 i.val L (by rw [← hfl]; exact hL) (hnL i)
    let ŵ : PriorSample s T d S Δ L → Vector d := fun ω =>
      deployed θ₀ π (priorTranscript (fun _ : Fin T => g0 hd θ₀ Δ) ω) i
    have hŵ : @Measurable _ _ (priorInformation (fun _ : Fin T => g0 hd θ₀ Δ) i.val)
        inferInstance ŵ :=
      @Measurable.comp _ _ _ (priorInformation (fun _ : Fin T => g0 hd θ₀ Δ) i.val)
        (information s T d i.val) _ _ _ (measurable_deployed θ₀ π hπ i.val)
        (@comap_measurable _ _ (information s T d i.val) (priorTranscript _))
    have hbad := hb ℓ (by rw [hfl]; exact hℓ0) hℓL i.val i.2.le hnℓ ŵ hŵ
    have hŵm : Measurable ŵ := hŵ.mono (priorInformation_le _ _) le_rfl
    set A : Set (PriorSample s T d S Δ L) := {ω | ‖blockProjection S (ŵ ω) -
      blockProjection S (g0 hd θ₀ Δ) - hiddenShift S Δ L ω.2.1‖ ≤
        levelAmplitude ℓ * Real.sqrt S.card / 16} with hAdef
    have hAm : MeasurableSet A := by
      refine measurableSet_le ?_ measurable_const
      exact (((measurable_blockProjection S).comp hŵm).sub measurable_const).sub
        ((measurable_hiddenShift S Δ L).comp (measurable_fst.comp measurable_snd)) |>.norm
    have hμ : ENNReal.ofReal (16 / 25) ≤ priorLaw s T d S Δ L Aᶜ := by
      rw [prob_compl_eq_one_sub hAm]
      have h1 : priorLaw s T d S Δ L A ≤ ENNReal.ofReal (9 / 25) :=
        hbad.trans (ENNReal.ofReal_le_ofReal (by
          rw [hcard]; exact pow_le_of_le_one (by norm_num) (by norm_num) hd.ne'))
      calc ENNReal.ofReal (16 / 25) = 1 - ENNReal.ofReal (9 / 25) := by
            rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]; norm_num
        _ ≤ 1 - priorLaw s T d S Δ L A := tsub_le_tsub_left h1 _
    have hM : 0 < max (i.val : ℝ) x0 := lt_max_of_lt_right hx0
    have hP : (0 : ℝ) < (2 : ℝ) ^ ℓ := by positivity
    have hρ := rho_le d hd _ _ hM hP hℓ2
    have hpt : ∀ ω, Aᶜ.indicator (fun _ => ENNReal.ofReal ((1 / 2 : ℝ) *
        ((2 : ℝ) ^ (-19 : ℤ) * d / max (i.val : ℝ) x0))) ω ≤
        ENNReal.ofReal ((1 / 2 : ℝ) * ‖deployed θ₀ π
          (priorTranscript (fun _ : Fin T => g0 hd θ₀ Δ) ω) i -
            (g0 hd θ₀ Δ + embedBlock S (hiddenShift S Δ L ω.2.1))‖ ^ 2) := by
      intro ω
      by_cases hω : ω ∈ Aᶜ
      · rw [Set.indicator_of_mem hω]
        apply ENNReal.ofReal_le_ofReal
        have hlt : levelAmplitude ℓ * Real.sqrt S.card / 16 <
            ‖blockProjection S (ŵ ω) - blockProjection S (g0 hd θ₀ Δ) -
              hiddenShift S Δ L ω.2.1‖ := by
          simpa [hAdef] using hω
        have hc0 : 0 ≤ levelAmplitude ℓ * Real.sqrt S.card / 16 := by
          unfold levelAmplitude; positivity
        have hsq := pow_lt_pow_left₀ hlt hc0 (two_ne_zero)
        have hc2 : (levelAmplitude ℓ * Real.sqrt S.card / 16) ^ 2 =
            (1 / 256) * ((2 : ℝ) ^ (-10 : ℤ) * ((2 : ℝ) ^ ℓ)⁻¹) * d := by
          rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), hcard]
          unfold levelAmplitude
          rw [Real.sq_sqrt (by positivity)]
          simp only [zpow_neg]
          ring
        have herr : ‖deployed θ₀ π (priorTranscript (fun _ : Fin T => g0 hd θ₀ Δ) ω) i -
            (g0 hd θ₀ Δ + embedBlock S (hiddenShift S Δ L ω.2.1))‖ =
            ‖blockProjection S (ŵ ω) - blockProjection S (g0 hd θ₀ Δ) -
              hiddenShift S Δ L ω.2.1‖ := err_eq _ _ _
        rw [herr]
        nlinarith [hsq, hc2, hρ]
      · rw [Set.indicator_of_notMem hω]; exact zero_le
    calc ENNReal.ofReal ((8 / 25 : ℝ) * ((2 : ℝ) ^ (-19 : ℤ) * d / max (i.val : ℝ) x0))
        = ENNReal.ofReal ((1 / 2 : ℝ) * ((2 : ℝ) ^ (-19 : ℤ) * d / max (i.val : ℝ) x0)) *
          ENNReal.ofReal (16 / 25) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) * ((2 : ℝ) ^ (-19 : ℤ) * d / max (i.val : ℝ) x0)) *
          priorLaw s T d S Δ L Aᶜ := by gcongr
      _ = ∫⁻ ω, Aᶜ.indicator (fun _ => ENNReal.ofReal ((1 / 2 : ℝ) *
          ((2 : ℝ) ^ (-19 : ℤ) * d / max (i.val : ℝ) x0))) ω ∂(priorLaw s T d S Δ L) :=
          (lintegral_indicator_const hAm.compl _).symm
      _ ≤ _ := lintegral_mono hpt
  have hsplit : ∀ ω, pathLoss θ₀ π (g0 hd θ₀ Δ) Δ L ω = ∑ i : Fin T,
      ENNReal.ofReal ((1 / 2 : ℝ) * ‖deployed θ₀ π
        (priorTranscript (fun _ : Fin T => g0 hd θ₀ Δ) ω) i -
          (g0 hd θ₀ Δ + embedBlock S (hiddenShift S Δ L ω.2.1))‖ ^ 2) := by
    intro ω
    unfold pathLoss
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  have hlhs : ENNReal.ofReal ((8 / 25 : ℝ) * (2 : ℝ) ^ (-19 : ℤ) * d *
      ∑ i : Fin T, 1 / max (i.val : ℝ) (16 * (d : ℝ) / Δ ^ 2)) =
      ∑ i : Fin T, ENNReal.ofReal ((8 / 25 : ℝ) *
        ((2 : ℝ) ^ (-19 : ℤ) * d / max (i.val : ℝ) x0)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hx0def]; ring
  rw [hlhs]
  calc ∑ i : Fin T, ENNReal.ofReal ((8 / 25 : ℝ) * ((2 : ℝ) ^ (-19 : ℤ) * d / max (i.val : ℝ) x0))
      ≤ ∑ i : Fin T, ∫⁻ ω, ENNReal.ofReal ((1 / 2 : ℝ) * ‖deployed θ₀ π
        (priorTranscript (fun _ : Fin T => g0 hd θ₀ Δ) ω) i -
          (g0 hd θ₀ Δ + embedBlock S (hiddenShift S Δ L ω.2.1))‖ ^ 2)
        ∂(priorLaw s T d S Δ L) := Finset.sum_le_sum fun i _ => hround i
    _ ≤ ∫⁻ ω, ∑ i : Fin T, ENNReal.ofReal ((1 / 2 : ℝ) * ‖deployed θ₀ π
        (priorTranscript (fun _ : Fin T => g0 hd θ₀ Δ) ω) i -
          (g0 hd θ₀ Δ + embedBlock S (hiddenShift S Δ L ω.2.1))‖ ^ 2)
        ∂(priorLaw s T d S Δ L) := sum_lintegral_le _ _ _
    _ = _ := lintegral_congr (fun ω => (hsplit ω).symm)

end TRS.Dev.GoalLower
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.GoalLower

open TRS.Dev.LowerErrorEventCore1 TRS.Dev.LowerErrorEventCore3

theorem phase_lower {s : RandomSeed} {T d B : ℕ} (hT : 0 < T) (hd : 0 < d) (θ₀ : Vector d)
    (Δ : ℝ) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1) (π : ReleasePolicy s T d B) (hπ : IsCausal π)
    (hxT : 16 * (d : ℝ) / Δ ^ 2 ≤ T)
    (hU : (B : ℝ) * ((Lv T d Δ - firstLevel (Finset.univ : Finset (Fin d)).card Δ + 1 : ℤ) : ℝ) *
      (9 / 25 : ℝ) ^ d ≤ 1 / 2) :
    ENNReal.ofReal ((2 : ℝ) ^ (-21 : ℤ) * d * (((B : ℝ) + 1) *
      (((T : ℝ) / (16 * (d : ℝ) / Δ ^ 2)) ^ (1 / ((B : ℝ) + 1)) - 1))) ≤ worstRisk θ₀ Δ π := by
  classical
  set S : Finset (Fin d) := Finset.univ with hSdef
  have hcard : S.card = d := by simp [S]
  have hS : 0 < S.card := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set x0 : ℝ := 16 * (d : ℝ) / Δ ^ 2 with hx0def
  have hx0 : 0 < x0 := by positivity
  set L := Lv T d Δ with hLdef
  have hL : firstLevel S.card Δ ≤ L := le_max_left _ _
  have hLT : (T : ℝ) ≤ (2 : ℝ) ^ L :=
    le_trans (le_zpow_ceil T (by exact_mod_cast hT))
      (zpow_le_zpow_right₀ (by norm_num) (le_max_right _ _))
  have key := common_lower_error_event T d hT hd S hS Δ hΔ hΔ₁ L hL hLT
    (fun _ => g0 hd θ₀ Δ) (blockProjection S (g0 hd θ₀ Δ)) (fun _ => rfl) s
  obtain ⟨hH, -, hc⟩ := key
  have hg0 : ‖g0 hd θ₀ Δ - θ₀‖ + Δ / 32 ≤ Δ := by rw [norm_g0 hd θ₀ Δ hΔ]; linarith
  refine le_trans ?_ (prior_le_worst θ₀ Δ π (g0 hd θ₀ Δ) L hg0 hH)
  haveI hprob : IsProbabilityMeasure (priorLaw s T d S Δ L) := by unfold priorLaw; infer_instance
  obtain ⟨E, hEm, hEμ, hE⟩ := hc B π hπ
  have hEμ' : ENNReal.ofReal (1 / 2) ≤ priorLaw s T d S Δ L E := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hEμ
    rw [hcard] at hU ⊢
    linarith
  set K : ℝ := ((B : ℝ) + 1) * (((T : ℝ) / x0) ^ (1 / ((B : ℝ) + 1)) - 1) with hK
  have hpath : ∀ ω ∈ E, ENNReal.ofReal ((2 : ℝ) ^ (-20 : ℤ) * d * K) ≤
      pathLoss θ₀ π (g0 hd θ₀ Δ) Δ L ω := by
    intro ω hω
    unfold pathLoss
    apply ENNReal.ofReal_le_ofReal
    set c0 : ℝ := (2 : ℝ) ^ (-19 : ℤ) * d with hc0
    have hc0pos : 0 < c0 := by positivity
    set err : Fin T → ℝ := fun i => ‖deployed θ₀ π (priorTranscript (fun _ : Fin T => g0 hd θ₀ Δ) ω) i -
      (g0 hd θ₀ Δ + embedBlock S (hiddenShift S Δ L ω.2.1))‖ with herr
    have hsum : K ≤ ∑ i : Fin T, err i ^ 2 / c0 := by
      refine phase_sum T B x0 hx0 hxT (fun j => π.date j (priorTranscript (fun _ : Fin T => g0 hd θ₀ Δ) ω))
        (fun a b hab => hπ.2.1 _ hab) (fun j => hπ.1 j _) (fun i => err i ^ 2 / c0) ?_
      intro i
      rcases deployed_spec θ₀ π (priorTranscript (fun _ : Fin T => g0 hd θ₀ Δ) ω) i with
        ⟨h1, h2⟩ | ⟨j, hj1, hj2, hj3⟩
      · left
        refine ⟨h2, ?_⟩
        have hnorm : Δ / 2 - Δ / 32 ≤ err i := by
          have e1 : err i = ‖(Δ / 2) • e0 hd + embedBlock S (hiddenShift S Δ L ω.2.1)‖ := by
            simp only [herr]
            rw [h1]
            unfold g0
            rw [← norm_neg]; congr 1; abel
          rw [e1]
          have h5 := norm_sub_norm_le ((Δ / 2) • e0 hd)
            (-(embedBlock S (hiddenShift S Δ L ω.2.1)))
          rw [sub_neg_eq_add, norm_neg, norm_embedBlock, norm_smul, norm_e0,
            Real.norm_eq_abs, abs_of_pos (by positivity)] at h5
          have := hH (ω.2.1)
          linarith
        have herr2 : Δ ^ 2 / 8 ≤ err i ^ 2 := by nlinarith
        rw [div_le_div_iff₀ hx0 hc0pos]
        have : x0 * Δ ^ 2 = 16 * d := by rw [hx0def]; field_simp
        have h6 : (2 : ℝ) ^ (-19 : ℤ) ≤ 1 := by norm_num
        calc 1 * c0 = (2 : ℝ) ^ (-19 : ℤ) * d := by rw [hc0]; ring
          _ ≤ 1 * d := by gcongr
          _ ≤ err i ^ 2 * x0 := by nlinarith
      · right
        refine ⟨j, hj1, hj3, ?_⟩
        have hjT : π.date j (priorTranscript (fun _ : Fin T => g0 hd θ₀ Δ) ω) < T := by
          have := i.2; omega
        have h4 := hE ω hω j hjT
        rw [hcard] at h4
        have herr : err i = ‖blockProjection S (π.head j (priorTranscript (fun _ : Fin T => g0 hd θ₀ Δ) ω)) -
            blockProjection S (g0 hd θ₀ Δ) - hiddenShift S Δ L ω.2.1‖ := by
          simp only [herr, hj2]; exact err_eq _ _ _
        rw [herr, le_div_iff₀ hc0pos]
        calc 1 / max (π.date j (priorTranscript (fun _ : Fin T => g0 hd θ₀ Δ) ω) : ℝ) x0 * c0
            = (2 : ℝ) ^ (-19 : ℤ) * d / max (π.date j (priorTranscript (fun _ : Fin T => g0 hd θ₀ Δ) ω) : ℝ)
              (16 * (d : ℝ) / Δ ^ 2) := by rw [hc0, hx0def]; ring
          _ ≤ _ := h4
    have h7 := mul_le_mul_of_nonneg_left hsum hc0pos.le
    rw [Finset.mul_sum] at h7
    show _ ≤ (1 / 2 : ℝ) * ∑ i : Fin T, err i ^ 2
    have h8 : ∀ i : Fin T, c0 * (err i ^ 2 / c0) = err i ^ 2 := fun i => by field_simp
    simp only [h8] at h7
    have : (2 : ℝ) ^ (-20 : ℤ) * d * K = (1 / 2) * (c0 * K) := by rw [hc0]; norm_num; ring
    rw [this]
    linarith
  calc ENNReal.ofReal ((2 : ℝ) ^ (-21 : ℤ) * d * K)
      = ENNReal.ofReal ((2 : ℝ) ^ (-20 : ℤ) * d * K) * ENNReal.ofReal (1 / 2) := by
        rw [← ENNReal.ofReal_mul' (by norm_num)]; congr 1; norm_num; ring
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (-20 : ℤ) * d * K) * priorLaw s T d S Δ L E := by gcongr
    _ = ∫⁻ ω, E.indicator (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (-20 : ℤ) * d * K)) ω
          ∂(priorLaw s T d S Δ L) := (lintegral_indicator_const hEm _).symm
    _ ≤ _ := by
        refine lintegral_mono fun ω => ?_
        by_cases hω : ω ∈ E
        · rw [Set.indicator_of_mem hω]; exact hpath ω hω
        · rw [Set.indicator_of_notMem hω]; exact zero_le

end TRS.Dev.GoalLower
end
end

section
set_option autoImplicit false
open scoped BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.GoalLower

lemma sum_lower_aux (x0 : ℝ) (hx0 : 0 < x0) (T : ℕ) :
    min (T : ℝ) x0 / x0 + Real.log (max (T : ℝ) x0 / x0) ≤
      ∑ i ∈ Finset.range T, 1 / max (i : ℝ) x0 := by
  induction T with
  | zero =>
    simp [hx0.le, div_self hx0.ne']
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    have hM : 0 < max (n : ℝ) x0 := lt_max_of_lt_right hx0
    suffices h : min ((n : ℝ) + 1) x0 / x0 + Real.log (max ((n : ℝ) + 1) x0 / x0) ≤
        min (n : ℝ) x0 / x0 + Real.log (max (n : ℝ) x0 / x0) + 1 / max (n : ℝ) x0 by linarith
    rcases le_or_gt x0 (n : ℝ) with h1 | h1
    · -- n ≥ x0
      have e1 : min ((n : ℝ) + 1) x0 = x0 := min_eq_right (by linarith)
      have e2 : min (n : ℝ) x0 = x0 := min_eq_right h1
      have e3 : max ((n : ℝ) + 1) x0 = n + 1 := max_eq_left (by linarith)
      have e4 : max (n : ℝ) x0 = n := max_eq_left h1
      rw [e1, e2, e3, e4]
      have hn0 : 0 < (n : ℝ) := lt_of_lt_of_le hx0 h1
      have : Real.log (((n : ℝ) + 1) / x0) = Real.log ((n : ℝ) / x0) + Real.log (((n : ℝ) + 1) / n) := by
        rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
      rw [this]
      have := Real.log_le_sub_one_of_pos (show 0 < ((n : ℝ) + 1) / n by positivity)
      have h2 : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
      linarith
    · rcases le_or_gt x0 ((n : ℝ) + 1) with h2 | h2
      · -- n < x0 ≤ n+1
        have e1 : min ((n : ℝ) + 1) x0 = x0 := min_eq_right h2
        have e2 : min (n : ℝ) x0 = n := min_eq_left h1.le
        have e3 : max ((n : ℝ) + 1) x0 = n + 1 := max_eq_left h2
        have e4 : max (n : ℝ) x0 = x0 := max_eq_right h1.le
        rw [e1, e2, e3, e4, div_self hx0.ne', Real.log_one]
        have := Real.log_le_sub_one_of_pos (show 0 < ((n : ℝ) + 1) / x0 by positivity)
        have h3 : ((n : ℝ) + 1) / x0 - 1 = ((n : ℝ) + 1) / x0 - 1 := rfl
        have h4 : (n : ℝ) / x0 + 1 / x0 = ((n : ℝ) + 1) / x0 := by ring
        have h5 : x0 / x0 = 1 := div_self hx0.ne'
        linarith
      · have e1 : min ((n : ℝ) + 1) x0 = n + 1 := min_eq_left h2.le
        have e2 : min (n : ℝ) x0 = n := min_eq_left h1.le
        have e3 : max ((n : ℝ) + 1) x0 = x0 := max_eq_right h2.le
        have e4 : max (n : ℝ) x0 = x0 := max_eq_right h1.le
        rw [e1, e2, e3, e4, div_self hx0.ne', Real.log_one]
        have : ((n : ℝ) + 1) / x0 = n / x0 + 1 / x0 := by ring
        linarith


lemma rpow_inv_eq (m : ℝ) (hm : 0 < m) (k : ℝ) :
    m ^ (1 / k) = Real.exp (Real.log m / k) := by
  rw [Real.rpow_def_of_pos hm]; congr 1; ring

lemma rate_eq (B : ℕ) (m : ℝ) (hm : 1 ≤ m) :
    releaseRate B m = 1 + ((B : ℝ) + 1) * (Real.exp (Real.log m / ((B : ℝ) + 1)) - 1) := by
  unfold releaseRate
  rw [if_neg (not_lt.2 hm), rpow_inv_eq m (by linarith)]

lemma exp_sub_one_le (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h := Real.add_one_le_exp (-x)
  have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos x]

lemma rate_le_m (B : ℕ) (m : ℝ) (hm : 0 < m) : releaseRate B m ≤ m := by
  by_cases h : m < 1
  · unfold releaseRate; rw [if_pos h]
  · push_neg at h
    unfold releaseRate
    rw [if_neg (not_lt.2 h)]
    have hk : (0 : ℝ) < (B : ℝ) + 1 := by positivity
    have := rpow_one_add_le_one_add_mul_self (s := m - 1) (by linarith)
      (p := 1 / ((B : ℝ) + 1)) (by positivity)
      (by rw [div_le_one hk]; linarith [(Nat.cast_nonneg B : (0 : ℝ) ≤ B)])
    rw [show (1 : ℝ) + (m - 1) = m by ring] at this
    have h2 : ((B : ℝ) + 1) * (m ^ (1 / ((B : ℝ) + 1)) - 1) ≤ m - 1 := by
      have : m ^ (1 / ((B : ℝ) + 1)) - 1 ≤ 1 / ((B : ℝ) + 1) * (m - 1) := by linarith
      calc ((B : ℝ) + 1) * (m ^ (1 / ((B : ℝ) + 1)) - 1)
          ≤ ((B : ℝ) + 1) * (1 / ((B : ℝ) + 1) * (m - 1)) := by gcongr
        _ = m - 1 := by field_simp
    linarith

lemma rate_le_16 (B : ℕ) (m : ℝ) (hm : 1 ≤ m)
    (h16 : Real.exp (Real.log m / ((B : ℝ) + 1)) ≤ 16) :
    releaseRate B m ≤ 1 + 16 * Real.log m := by
  rw [rate_eq B m hm]
  have hk : (0 : ℝ) < (B : ℝ) + 1 := by positivity
  set x := Real.log m / ((B : ℝ) + 1) with hx
  have hx0 : 0 ≤ x := div_nonneg (Real.log_nonneg hm) hk.le
  have h1 := exp_sub_one_le x
  have h2 : x * Real.exp x ≤ x * 16 := by gcongr
  have h3 : ((B : ℝ) + 1) * x = Real.log m := by rw [hx]; field_simp
  have : ((B : ℝ) + 1) * (Real.exp x - 1) ≤ ((B : ℝ) + 1) * (x * 16) := by gcongr; linarith
  nlinarith


lemma log16 : Real.log 16 = 4 * Real.log 2 := by
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num

lemma log256 : Real.log 256 = 8 * Real.log 2 := by
  rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num

lemma exp_le_of_le_log (a y : ℝ) (hy : 0 < y) (h : a ≤ Real.log y) : Real.exp a ≤ y := by
  calc Real.exp a ≤ Real.exp (Real.log y) := Real.exp_le_exp.2 h
    _ = y := Real.exp_log hy

lemma round_numeric (B : ℕ) (hB : 1 ≤ B) (T : ℕ) (hT : 0 < T) (x0 : ℝ) (hx0 : 0 < x0)
    (m : ℝ) (hm : m = 16 * T / x0)
    (hreg : m < 256 ∨ (256 ≤ m ∧ Real.log m ≤ (B : ℝ) + 1)) :
    releaseRate B m ≤ 81 * (min (T : ℝ) x0 / x0 + Real.log (max (T : ℝ) x0 / x0)) := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hmpos : 0 < m := by rw [hm]; positivity
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  rcases le_or_gt m 16 with h16 | h16
  · have hTx : (T : ℝ) ≤ x0 := by
      rw [hm, div_le_iff₀ hx0] at h16; linarith
    rw [min_eq_left hTx, max_eq_right hTx, div_self hx0.ne', Real.log_one]
    have := rate_le_m B m hmpos
    have h2 : m = 16 * ((T : ℝ) / x0) := by rw [hm]; ring
    have h3 : (0 : ℝ) < (T : ℝ) / x0 := by positivity
    nlinarith
  · have hxT : x0 ≤ (T : ℝ) := by
      rw [hm, lt_div_iff₀ hx0] at h16; linarith
    rw [min_eq_right hxT, max_eq_left hxT, div_self hx0.ne']
    have hm1 : 1 ≤ m := by linarith
    have hlogm : Real.log 16 < Real.log m := Real.log_lt_log (by norm_num) h16
    have hk : (2 : ℝ) ≤ (B : ℝ) + 1 := by
      have : (1 : ℝ) ≤ B := by exact_mod_cast hB
      linarith
    have hlm0 : 0 ≤ Real.log m := Real.log_nonneg hm1
    have hexp : Real.exp (Real.log m / ((B : ℝ) + 1)) ≤ 16 := by
      rcases hreg with h256 | ⟨h256, hlog⟩
      · apply exp_le_of_le_log _ _ (by norm_num)
        have h1 : Real.log m < Real.log 256 := Real.log_lt_log hmpos h256
        have h2 : Real.log m / ((B : ℝ) + 1) ≤ Real.log m / 2 :=
          div_le_div_of_nonneg_left hlm0 (by norm_num) hk
        rw [log256] at h1
        rw [log16]
        linarith
      · have h2 : Real.log m / ((B : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by linarith)]; exact hlog
        have h3 := Real.exp_one_lt_d9
        have h4 : Real.exp (Real.log m / ((B : ℝ) + 1)) ≤ Real.exp 1 := Real.exp_le_exp.2 h2
        linarith
    have hΛ := rate_le_16 B m hm1 hexp
    have hdiv : Real.log ((T : ℝ) / x0) = Real.log m - Real.log 16 := by
      rw [← Real.log_div hmpos.ne' (by norm_num)]
      congr 1; rw [hm]; field_simp
    rw [hdiv, log16]
    rw [log16] at hlogm
    nlinarith


lemma phase_numeric (B : ℕ) (m r : ℝ) (hm : 256 ≤ m) (hr : r = m / 16) :
    releaseRate B m ≤ 64 * (((B : ℝ) + 1) * (r ^ (1 / ((B : ℝ) + 1)) - 1)) := by
  have hmpos : 0 < m := by linarith
  have hk : (1 : ℝ) ≤ (B : ℝ) + 1 := by linarith [(Nat.cast_nonneg B : (0 : ℝ) ≤ B)]
  have hk0 : (0 : ℝ) < (B : ℝ) + 1 := by linarith
  have hl2 := Real.log_two_gt_d9
  have hlm : 8 * Real.log 2 ≤ Real.log m := by
    rw [← log256]; exact Real.log_le_log (by norm_num) hm
  set k : ℝ := (B : ℝ) + 1 with hkdef
  set b : ℝ := Real.log m / k with hb
  set a : ℝ := Real.log 16 / k with ha
  have hkb : k * b = Real.log m := by rw [hb]; field_simp
  have hka : k * a = Real.log 16 := by rw [ha]; field_simp
  have hr0 : 0 < r := by rw [hr]; positivity
  have hlogr : Real.log r = Real.log m - Real.log 16 := by
    rw [hr, Real.log_div hmpos.ne' (by norm_num)]
  have hrpow : r ^ (1 / k) = Real.exp (b - a) := by
    rw [rpow_inv_eq r hr0, hlogr, hb, ha]; congr 1; ring
  rw [hrpow, rate_eq B m (by linarith)]
  rw [← hkdef, ← hb]
  have ha0 : 0 ≤ a := div_nonneg (by rw [log16]; linarith) hk0.le
  have hb2 : 2 * a ≤ b := by
    have : k * (2 * a) ≤ k * b := by
      have e : k * (2 * a) = 2 * (k * a) := by ring
      rw [e, hka, hkb, log16]; linarith
    exact le_of_mul_le_mul_left this hk0
  have hale : a ≤ Real.log 16 := by
    have : k * a ≤ k * Real.log 16 := by rw [hka]; nlinarith [(by rw [log16]; linarith : 0 ≤ Real.log 16)]
    exact le_of_mul_le_mul_left this hk0
  have hb0 : 0 ≤ b := by linarith
  have hea : (1 / 16 : ℝ) ≤ Real.exp (-a) := by
    have : Real.exp (-Real.log 16) ≤ Real.exp (-a) := Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_neg, Real.exp_log (by norm_num)] at this
    linarith
  set w : ℝ := Real.exp (b / 2) with hw
  have hw1 : 1 ≤ w := by rw [hw]; exact Real.one_le_exp (by linarith)
  have hwsq : Real.exp b = w ^ 2 := by rw [hw, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hexpba : Real.exp (b - a) = Real.exp b * Real.exp (-a) := by rw [← Real.exp_add]; ring_nf
  have hclaim : (Real.exp b - 1) / 32 ≤ Real.exp (b - a) - 1 := by
    rcases le_or_gt 31 (w ^ 2) with h31 | h31
    · rw [hexpba, hwsq]
      have : w ^ 2 * (1 / 16) ≤ w ^ 2 * Real.exp (-a) := by gcongr
      linarith
    · have h1 : w ≤ Real.exp (b - a) := Real.exp_le_exp.2 (by linarith)
      rw [hwsq]
      nlinarith
  have hkb2 : 1 ≤ k * (Real.exp b - 1) := by
    have : b ≤ Real.exp b - 1 := by linarith [Real.add_one_le_exp b]
    have h2 : k * b ≤ k * (Real.exp b - 1) := by gcongr
    rw [hkb] at h2
    linarith
  nlinarith

end TRS.Dev.GoalLower
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.GoalLower

lemma union_bound (T d B : ℕ) (hT : 0 < T) (hd : 0 < d) (Δ : ℝ) (hΔ : 0 < Δ)
    (hm : 256 ≤ effectiveHorizon T d Δ)
    (hB : (B : ℝ) + 1 < Real.log (effectiveHorizon T d Δ))
    (hdim : 1 + 2 * logTwo (logTwo (effectiveHorizon T d Δ)) ≤ (d : ℝ)) :
    (B : ℝ) * ((Lv T d Δ - firstLevel (Finset.univ : Finset (Fin d)).card Δ + 1 : ℤ) : ℝ) *
      (9 / 25 : ℝ) ^ d ≤ 1 / 2 := by
  set m := effectiveHorizon T d Δ with hmdef
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hmpos : 0 < m := by linarith
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  set lm : ℝ := logTwo m with hlm
  have hlmdef : lm = Real.log m / Real.log 2 := rfl
  have hlogm : 8 * Real.log 2 ≤ Real.log m := by
    rw [← log256]; exact Real.log_le_log (by norm_num) hm
  have hlm8 : 8 ≤ lm := by
    rw [hlmdef, le_div_iff₀ (by linarith)]; linarith
  have hlm0 : 0 < lm := by linarith
  have hBlm : (B : ℝ) ≤ lm := by
    have : Real.log m ≤ lm := by
      rw [hlmdef, le_div_iff₀ (by linarith)]; nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ m by linarith)]
    linarith
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  -- bound on the number of levels
  have hx0 : (0 : ℝ) < 16 * (d : ℝ) / Δ ^ 2 := by positivity
  have hmx : (T : ℝ) / (16 * (d : ℝ) / Δ ^ 2) = m / 16 := by
    rw [hmdef]; unfold effectiveHorizon; field_simp
  have hN : ((Lv T d Δ - firstLevel (Finset.univ : Finset (Fin d)).card Δ + 1 : ℤ) : ℝ) ≤ lm := by
    rw [firstLevel_univ]
    unfold Lv
    rw [firstLevel_univ]
    rcases le_total ⌈Real.logb 2 (16 * (d : ℝ) / Δ ^ 2)⌉ ⌈Real.logb 2 (T : ℝ)⌉ with h | h
    · rw [max_eq_right h]
      push_cast
      have h1 : (⌈Real.logb 2 (T : ℝ)⌉ : ℝ) < Real.logb 2 T + 1 := Int.ceil_lt_add_one _
      have h2 : Real.logb 2 (16 * (d : ℝ) / Δ ^ 2) ≤ (⌈Real.logb 2 (16 * (d : ℝ) / Δ ^ 2)⌉ : ℝ) :=
        Int.le_ceil _
      have h3 : Real.logb 2 (T : ℝ) - Real.logb 2 (16 * (d : ℝ) / Δ ^ 2) = lm - 4 := by
        unfold Real.logb
        rw [← sub_div, ← Real.log_div hTpos.ne' hx0.ne', hmx, Real.log_div hmpos.ne' (by norm_num),
          log16, hlmdef]
        field_simp
      linarith
    · rw [max_eq_left h]; push_cast; linarith
  have hN0 : (0 : ℝ) ≤ ((Lv T d Δ - firstLevel (Finset.univ : Finset (Fin d)).card Δ + 1 : ℤ) : ℝ) := by
    have : firstLevel (Finset.univ : Finset (Fin d)).card Δ ≤ Lv T d Δ := le_max_left _ _
    have : (0 : ℤ) ≤ Lv T d Δ - firstLevel (Finset.univ : Finset (Fin d)).card Δ + 1 := by omega
    exact_mod_cast this
  set N : ℝ := ((Lv T d Δ - firstLevel (Finset.univ : Finset (Fin d)).card Δ + 1 : ℤ) : ℝ) with hNdef
  -- 2^d ≥ 2 lm²
  have h2d : 2 * lm ^ 2 ≤ (2 : ℝ) ^ d := by
    have hd2 : 1 + 2 * Real.logb 2 lm ≤ (d : ℝ) := hdim
    have h5 : ((2 : ℝ) ^ (Real.logb 2 lm)) = lm := Real.rpow_logb (by norm_num) (by norm_num) hlm0
    have e : (2 : ℝ) ^ (1 + 2 * Real.logb 2 lm) = 2 * lm ^ 2 := by
      rw [Real.rpow_add (by norm_num), Real.rpow_one, mul_comm 2 (Real.logb 2 lm),
        Real.rpow_mul (by norm_num), h5, Real.rpow_two]
    have : (2 : ℝ) ^ (1 + 2 * Real.logb 2 lm) ≤ (2 : ℝ) ^ (d : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hd2
    rw [Real.rpow_natCast, e] at this
    exact this
  have h925 : (9 / 25 : ℝ) ^ d ≤ ((2 : ℝ) ^ d)⁻¹ := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) d
  have hlm2 : 0 < lm ^ 2 := by positivity
  have h2inv : ((2 : ℝ) ^ d)⁻¹ ≤ (2 * lm ^ 2)⁻¹ := inv_anti₀ (by positivity) h2d
  have hBN : (B : ℝ) * N ≤ lm * lm := mul_le_mul hBlm hN hN0 hlm0.le
  calc (B : ℝ) * N * (9 / 25 : ℝ) ^ d ≤ (lm * lm) * (2 * lm ^ 2)⁻¹ := by
        apply mul_le_mul hBN (h925.trans h2inv) (by positivity) (by positivity)
    _ = 1 / 2 := by field_simp

end TRS.Dev.GoalLower
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.GoalLower

lemma worstRisk_zero (T d : ℕ) (hd : 0 < d) (θ₀ : Vector d) (Δ : ℝ) (hΔ : 0 < Δ)
    {s : RandomSeed} (π : ReleasePolicy s T d 0) :
    worstRisk θ₀ Δ π = ENNReal.ofReal ((T : ℝ) * Δ ^ 2 / 2) := by
  have hrisk : ∀ θ : Vector d, policyRisk θ₀ π (fun _ => θ) =
      ENNReal.ofReal ((T : ℝ) * ‖θ₀ - θ‖ ^ 2 / 2) := by
    intro θ
    unfold policyRisk
    have hdep : ∀ (ω : Transcript s T d) (i : Fin T), deployed θ₀ π ω i = θ₀ := by
      intro ω i; simp [deployed]
    simp only [hdep]
    rw [lintegral_const, measure_univ, mul_one]
    congr 1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  unfold worstRisk
  apply le_antisymm
  · apply iSup_le
    rintro ⟨θ, hθ⟩
    show policyRisk θ₀ π (fun _ => θ) ≤ _
    rw [hrisk]
    apply ENNReal.ofReal_le_ofReal
    have : ‖θ₀ - θ‖ ≤ Δ := by rw [norm_sub_rev]; exact hθ
    have h0 := norm_nonneg (θ₀ - θ)
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    have h2 : ‖θ₀ - θ‖ ^ 2 ≤ Δ ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left h2 hT0
    linarith
  · let e : Vector d := EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ)
    have he : ‖e‖ = 1 := by simp [e]
    have hmem : ‖(θ₀ + Δ • e) - θ₀‖ ≤ Δ := by
      rw [add_sub_cancel_left, norm_smul, he, Real.norm_eq_abs, abs_of_pos hΔ]; simp
    refine le_trans ?_ (le_iSup _ ⟨θ₀ + Δ • e, hmem⟩)
    show _ ≤ policyRisk θ₀ π (fun _ => θ₀ + Δ • e)
    rw [hrisk]
    apply ENNReal.ofReal_le_ofReal
    have : ‖θ₀ - (θ₀ + Δ • e)‖ = Δ := by
      rw [sub_add_cancel_left, norm_neg, norm_smul, he, Real.norm_eq_abs, abs_of_pos hΔ]; simp
    rw [this]

theorem worst_lower {s : RandomSeed} {T d B : ℕ} (hT : 0 < T) (hd : 0 < d) (θ₀ : Vector d)
    (Δ : ℝ) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1) (π : ReleasePolicy s T d B) (hπ : IsCausal π)
    (hreg : lowerBoundRegime T d B Δ) :
    ENNReal.ofReal ((2 : ℝ) ^ (-27 : ℤ) * (d : ℝ) *
      releaseRate B (effectiveHorizon T d Δ)) ≤ worstRisk θ₀ Δ π := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  set m := effectiveHorizon T d Δ with hmdef
  have hmpos : 0 < m := by rw [hmdef]; unfold effectiveHorizon; positivity
  set x0 : ℝ := 16 * (d : ℝ) / Δ ^ 2 with hx0def
  have hx0 : 0 < x0 := by positivity
  have hmx : m = 16 * T / x0 := by
    rw [hmdef, hx0def]; unfold effectiveHorizon; field_simp
  have hTx : (T : ℝ) / x0 = m / 16 := by rw [hmx]; field_simp
  rcases Nat.eq_zero_or_pos B with hB0 | hB1
  · subst hB0
    have hrate := rate_le_m 0 m hmpos
    rw [worstRisk_zero T d hd θ₀ Δ hΔ π]
    apply ENNReal.ofReal_le_ofReal
    have hdm : (d : ℝ) * m = T * Δ ^ 2 := by
      rw [hmdef]; unfold effectiveHorizon; field_simp
    have h27 : (2 : ℝ) ^ (-27 : ℤ) ≤ 1 / 2 := by norm_num
    have : (2 : ℝ) ^ (-27 : ℤ) * d * releaseRate 0 m ≤ (1 / 2) * (d * m) := by
      have h1 : (d : ℝ) * releaseRate 0 m ≤ d * m := by gcongr
      calc (2 : ℝ) ^ (-27 : ℤ) * d * releaseRate 0 m = (2 : ℝ) ^ (-27 : ℤ) * (d * releaseRate 0 m) := by ring
        _ ≤ (2 : ℝ) ^ (-27 : ℤ) * (d * m) := by gcongr
        _ ≤ (1 / 2) * (d * m) := mul_le_mul_of_nonneg_right h27 (by positivity)
    rw [hdm] at this
    linarith
  · have hB : 1 ≤ B := hB1
    unfold lowerBoundRegime at hreg
    simp only at hreg
    by_cases hround : m < 256 ∨ (256 ≤ m ∧ Real.log m ≤ (B : ℝ) + 1)
    · -- per-round argument
      have hR := round_lower hT hd θ₀ Δ hΔ hΔ₁ π hπ
      refine le_trans ?_ hR
      apply ENNReal.ofReal_le_ofReal
      have hΛ := round_numeric B hB T hT x0 hx0 m hmx hround
      have hs := sum_lower_aux x0 hx0 T
      have hfin : ∑ i : Fin T, 1 / max (i.val : ℝ) x0 = ∑ i ∈ Finset.range T, 1 / max (i : ℝ) x0 :=
        Fin.sum_univ_eq_sum_range (fun i => 1 / max (i : ℝ) x0) T
      rw [← hx0def, hfin]
      have h1 : (2 : ℝ) ^ (-27 : ℤ) * 81 ≤ (8 / 25 : ℝ) * (2 : ℝ) ^ (-19 : ℤ) := by norm_num
      have h2 : releaseRate B m ≤ 81 * ∑ i ∈ Finset.range T, 1 / max (i : ℝ) x0 := by linarith
      have h3 : (2 : ℝ) ^ (-27 : ℤ) * releaseRate B m ≤
          (8 / 25 : ℝ) * (2 : ℝ) ^ (-19 : ℤ) * ∑ i ∈ Finset.range T, 1 / max (i : ℝ) x0 := by
        calc (2 : ℝ) ^ (-27 : ℤ) * releaseRate B m
            ≤ (2 : ℝ) ^ (-27 : ℤ) * (81 * ∑ i ∈ Finset.range T, 1 / max (i : ℝ) x0) := by gcongr
          _ = ((2 : ℝ) ^ (-27 : ℤ) * 81) * ∑ i ∈ Finset.range T, 1 / max (i : ℝ) x0 := by ring
          _ ≤ _ := by gcongr
      calc (2 : ℝ) ^ (-27 : ℤ) * d * releaseRate B m
          = d * ((2 : ℝ) ^ (-27 : ℤ) * releaseRate B m) := by ring
        _ ≤ d * ((8 / 25 : ℝ) * (2 : ℝ) ^ (-19 : ℤ) * ∑ i ∈ Finset.range T, 1 / max (i : ℝ) x0) := by
          gcongr
        _ = _ := by ring
    · -- common event argument
      push Not at hround
      have hm256 : 256 ≤ m := hround.1
      have hlog : (B : ℝ) + 1 < Real.log m := hround.2 hm256
      have hdim : 1 + 2 * logTwo (logTwo m) ≤ (d : ℝ) := by
        rcases hreg with h | ⟨_, h | h⟩
        · exact absurd h (not_lt.2 hm256)
        · exact absurd h (not_le.2 hlog)
        · exact h
      have hxT : x0 ≤ (T : ℝ) := by
        have : 1 ≤ (T : ℝ) / x0 := by rw [hTx]; linarith
        rwa [one_le_div hx0] at this
      have hU := union_bound T d B hT hd Δ hΔ hm256 hlog hdim
      have hP := phase_lower hT hd θ₀ Δ hΔ hΔ₁ π hπ hxT hU
      refine le_trans ?_ hP
      apply ENNReal.ofReal_le_ofReal
      have hnum := phase_numeric B m ((T : ℝ) / x0) hm256 (by rw [hTx])
      rw [← hx0def]
      have h1 : (2 : ℝ) ^ (-27 : ℤ) * 64 = (2 : ℝ) ^ (-21 : ℤ) := by norm_num
      calc (2 : ℝ) ^ (-27 : ℤ) * d * releaseRate B m
          ≤ (2 : ℝ) ^ (-27 : ℤ) * d * (64 * (((B : ℝ) + 1) *
            (((T : ℝ) / x0) ^ (1 / ((B : ℝ) + 1)) - 1))) := by gcongr
        _ = (2 : ℝ) ^ (-21 : ℤ) * d * (((B : ℝ) + 1) *
            (((T : ℝ) / x0) ^ (1 / ((B : ℝ) + 1)) - 1)) := by rw [← h1]; ring

theorem lower_part (T d B : ℕ) (hT : 0 < T) (hd : 0 < d)
    (θ₀ : Vector d) (Δ : ℝ) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1) :
    lowerBoundRegime T d B Δ →
      ENNReal.ofReal ((2 : ℝ) ^ (-27 : ℤ) * (d : ℝ) *
        releaseRate B (effectiveHorizon T d Δ)) ≤
        TightReleaseSchedules.Stationary.minimaxRisk T d B θ₀ Δ := by
  intro hreg
  unfold TightReleaseSchedules.Stationary.minimaxRisk
  apply le_sInf
  rintro v ⟨s, π, hπ, rfl⟩
  exact worst_lower hT hd θ₀ Δ hΔ hΔ₁ π hπ hreg

end TRS.Dev.GoalLower
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace TRS

open TightReleaseSchedules.Stationary

theorem chk_stationary_shift_release_budget (T d B : ℕ) (hT : 0 < T) (hd : 0 < d)
    (θ₀ : Vector d) (Δ : ℝ) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1) :
    TightReleaseSchedules.Stationary.minimaxRisk T d B θ₀ Δ ≤
      ENNReal.ofReal (5 * (d : ℝ) * releaseRate B (effectiveHorizon T d Δ)) ∧
    IsCausal (geometricPolicy T d B θ₀ Δ) ∧
    HasDeterministicDates (geometricPolicy T d B θ₀ Δ) ∧
    worstRisk θ₀ Δ (geometricPolicy T d B θ₀ Δ) ≤
      ENNReal.ofReal (5 * (d : ℝ) * releaseRate B (effectiveHorizon T d Δ)) ∧
    (lowerBoundRegime T d B Δ →
      ENNReal.ofReal ((2 : ℝ) ^ (-27 : ℤ) * (d : ℝ) *
        releaseRate B (effectiveHorizon T d Δ)) ≤
          TightReleaseSchedules.Stationary.minimaxRisk T d B θ₀ Δ) ∧
    (B = 0 → TightReleaseSchedules.Stationary.minimaxRisk T d B θ₀ Δ =
      ENNReal.ofReal ((T : ℝ) * Δ ^ 2 / 2)) := by
  have hu := TRS.Dev.GoalUpper.upper_parts T d B hT hd θ₀ Δ hΔ hΔ₁
  exact ⟨hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1,
    TRS.Dev.GoalLower.lower_part T d B hT hd θ₀ Δ hΔ hΔ₁, hu.2.2.2.2⟩

end TRS
end

theorem solution : type_of% @TRS.chk_stationary_shift_release_budget := @TRS.chk_stationary_shift_release_budget
