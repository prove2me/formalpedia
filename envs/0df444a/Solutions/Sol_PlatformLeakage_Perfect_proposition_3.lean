-- Prove2me | solution 1 for PlatformLeakage.Perfect.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T14:57:52.409888+00:00
-- url     : https://prove2.me/submissions/a76a0dd1-1752-470f-8e26-5221675899dc

import Mathlib
import Definitions.Def_PlatformLeakage_Perfect_Model

set_option autoImplicit false

namespace PL3Aux

open PlatformLeakage.Perfect

lemma frac_mono {A z1 z2 : ℝ} (hA : 0 < A) (h1 : 0 ≤ z1) (h12 : z1 ≤ z2) :
    z1 / (A + z1) ≤ z2 / (A + z2) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- the revenue identity behind the closed forms of (16)/(17) -/
lemma rev_gap (A μ n u x : ℝ) (hA : 0 < A) (hn : 0 < n) (hx : 0 < x) :
    A * μ / n * (u - 1) ^ 2 - (A * (u ^ 2 - 1) / n - x) * (μ * (n * x / (A + n * x))) =
      μ * (n * x - A * (u - 1)) ^ 2 / (n * (A + n * x)) := by
  have h1 : (A + n * x) ≠ 0 := by positivity
  field_simp
  ring

lemma rev_le (A μ n u ζ : ℝ) (hA : 0 < A) (hμ : 0 < μ) (hn : 0 < n) (hu : 1 < u)
    (hζ : 0 ≤ ζ) :
    ζ * (μ * (n * max (A * (u ^ 2 - 1) / n - ζ) 0 / (A + n * max (A * (u ^ 2 - 1) / n - ζ) 0)))
      ≤ A * μ / n * (u - 1) ^ 2 := by
  rcases le_or_gt (A * (u ^ 2 - 1) / n - ζ) 0 with h | h
  · rw [max_eq_right h]; simp; positivity
  · rw [max_eq_left h.le]
    generalize hx : A * (u ^ 2 - 1) / n - ζ = x at h ⊢
    have hz : ζ = A * (u ^ 2 - 1) / n - x := by linarith
    subst hz
    have := rev_gap A μ n u x hA hn h
    have : 0 ≤ μ * (n * x - A * (u - 1)) ^ 2 / (n * (A + n * x)) := by positivity
    linarith

lemma rev_eq (A μ n u ζ : ℝ) (hA : 0 < A) (hμ : 0 < μ) (hn : 0 < n) (hu : 1 < u)
    (hζ : 0 ≤ ζ)
    (heq : A * μ / n * (u - 1) ^ 2 ≤
      ζ * (μ * (n * max (A * (u ^ 2 - 1) / n - ζ) 0 / (A + n * max (A * (u ^ 2 - 1) / n - ζ) 0)))) :
    μ * (n * max (A * (u ^ 2 - 1) / n - ζ) 0 / (A + n * max (A * (u ^ 2 - 1) / n - ζ) 0))
      = μ * (u - 1) / u := by
  have hM : 0 < A * μ / n * (u - 1) ^ 2 := by
    have : 0 < u - 1 := by linarith
    positivity
  rcases le_or_gt (A * (u ^ 2 - 1) / n - ζ) 0 with h | h
  · rw [max_eq_right h] at heq; simp at heq; linarith
  · rw [max_eq_left h.le] at heq ⊢
    generalize hx : A * (u ^ 2 - 1) / n - ζ = x at h heq ⊢
    have hz : ζ = A * (u ^ 2 - 1) / n - x := by linarith
    subst hz
    have hg := rev_gap A μ n u x hA hn h
    have h0 : μ * (n * x - A * (u - 1)) ^ 2 / (n * (A + n * x)) = 0 := by
      have : 0 ≤ μ * (n * x - A * (u - 1)) ^ 2 / (n * (A + n * x)) := by positivity
      linarith
    have hpos : 0 < n * (A + n * x) := by positivity
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · have : (n * x - A * (u - 1)) ^ 2 = 0 := by
        rcases mul_eq_zero.mp h0 with h0 | h0
        · linarith
        · exact h0
      have hnx : n * x = A * (u - 1) := by nlinarith [sq_nonneg (n * x - A * (u - 1))]
      rw [hnx]
      have hu0 : u ≠ 0 := by positivity
      rw [show A + A * (u - 1) = A * u by ring, mul_div_mul_left _ _ hA.ne']
      ring
    · linarith

lemma rev_greatest (A μ n u : ℝ) (hA : 0 < A) (hμ : 0 < μ) (hn : 0 < n) (hu : 1 < u) :
    IsGreatest ((fun ζ : ℝ => ζ * (μ * (n * max (A * (u ^ 2 - 1) / n - ζ) 0 /
      (A + n * max (A * (u ^ 2 - 1) / n - ζ) 0)))) '' Set.Ici 0) (A * μ / n * (u - 1) ^ 2) := by
  refine ⟨⟨A * u * (u - 1) / n, ?_, ?_⟩, ?_⟩
  · simp only [Set.mem_Ici]
    have : 0 < u - 1 := by linarith
    positivity
  · simp only
    have hx : A * (u ^ 2 - 1) / n - A * u * (u - 1) / n = A * (u - 1) / n := by
      field_simp; ring
    have hu1 : 0 < u - 1 := by linarith
    have hx0 : 0 ≤ A * (u - 1) / n := by positivity
    rw [hx, max_eq_left hx0]
    have hu0 : u ≠ 0 := by positivity
    field_simp
    ring
  · rintro y ⟨ζ, hζ, rfl⟩
    exact rev_le A μ n u ζ hA hμ hn hu hζ

lemma sq_lt_iff {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : x ^ 2 < y ^ 2 ↔ x < y := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have := mul_le_mul hc hc hy hx
    nlinarith
  · intro h
    have := mul_lt_mul'' h h hx hx
    nlinarith

lemma h_sign (A μ N v Ro u t r : ℝ) (hA : 0 < A) (hμ : 0 < μ) (hN : 1 ≤ N) (hv : 0 < v)
    (hRo : 0 ≤ Ro) (hu : u = Real.sqrt (1 + N * v / A))
    (ht : t = Real.sqrt (1 + max (v - Ro) 0 / A)) (hr : r = Real.sqrt ((N - 1) / N)) :
    (A * μ / N * (u - 1) ^ 2 - A * μ * (t - 1) ^ 2 - Ro * (μ * (u - 1) / u) < 0 ↔
      v + A * (1 - ((1 - r) * u + r) ^ 2) < Ro) ∧
    (0 < A * μ / N * (u - 1) ^ 2 - A * μ * (t - 1) ^ 2 - Ro * (μ * (u - 1) / u) ↔
      Ro < v + A * (1 - ((1 - r) * u + r) ^ 2)) := by
  have hN0 : 0 < N := by linarith
  have hu2 : u ^ 2 = 1 + N * v / A := by rw [hu]; exact Real.sq_sqrt (by positivity)
  have hu0 : 0 ≤ u := hu ▸ Real.sqrt_nonneg _
  have hNvA : 0 < N * v / A := by positivity
  have hu1 : 1 < u := by nlinarith
  have hr2 : r ^ 2 = (N - 1) / N := by
    rw [hr]; exact Real.sq_sqrt (div_nonneg (by linarith) hN0.le)
  have hr0 : 0 ≤ r := hr ▸ Real.sqrt_nonneg _
  have hrN : N * r ^ 2 = N - 1 := by rw [hr2]; field_simp
  have hr21 : r ^ 2 < 1 := by rw [hr2, div_lt_one hN0]; linarith
  have hr1 : r < 1 := by
    have := (sq_lt_iff hr0 zero_le_one).mp (by simpa using hr21)
    exact this
  have hvv : v = A * (u ^ 2 - 1) / N := by
    rw [hu2]; field_simp; try ring
  have hm1 : 1 < (1 - r) * u + r := by nlinarith [mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hu1)]
  have hm0 : 0 ≤ (1 - r) * u + r := by linarith
  have hupos : 0 < u := by linarith
  rcases le_or_gt Ro v with hRv | hRv
  · have hmx : max (v - Ro) 0 = v - Ro := max_eq_left (by linarith)
    rw [hmx] at ht
    have ht2 : t ^ 2 = 1 + (v - Ro) / A := by rw [ht]; exact Real.sq_sqrt (by
      have : 0 ≤ (v - Ro) / A := div_nonneg (by linarith) hA.le
      linarith)
    have ht0 : 0 ≤ t := ht ▸ Real.sqrt_nonneg _
    have htu : t ≤ u := by
      rw [ht, hu]
      apply Real.sqrt_le_sqrt
      have : (v - Ro) / A ≤ N * v / A := by
        apply div_le_div_of_nonneg_right _ hA.le
        nlinarith
      linarith
    have hRo' : Ro = v - A * (t ^ 2 - 1) := by
      rw [ht2]; field_simp; try ring
    have hE : (A * μ / N * (u - 1) ^ 2 - A * μ * (t - 1) ^ 2 - Ro * (μ * (u - 1) / u)) * (u * N)
        = A * μ * N * ((r * (u - 1) - (u - t)) * (r * (u - 1) + (u - t))) := by
      have e1 : (A * μ / N * (u - 1) ^ 2 - A * μ * (t - 1) ^ 2 - Ro * (μ * (u - 1) / u)) * (u * N)
          = A * μ * u * (u - 1) ^ 2 - A * μ * N * u * (t - 1) ^ 2 - N * Ro * μ * (u - 1) := by
        field_simp
        try ring
      rw [e1, hRo']
      have e2 : N * (v - A * (t ^ 2 - 1)) = A * (u ^ 2 - 1) - N * A * (t ^ 2 - 1) := by
        rw [hvv]; field_simp; try ring
      have e3 : N * (v - A * (t ^ 2 - 1)) * μ * (u - 1)
          = (A * (u ^ 2 - 1) - N * A * (t ^ 2 - 1)) * μ * (u - 1) := by rw [e2]
      linear_combination (-1 : ℝ) * e3 - (A * μ * (u - 1) ^ 2) * hrN
    have hRoa : v + A * (1 - ((1 - r) * u + r) ^ 2) < Ro ↔ t < (1 - r) * u + r := by
      rw [hRo', ← sq_lt_iff ht0 hm0]
      constructor
      · intro h
        by_contra hc
        push Not at hc
        have := mul_le_mul_of_nonneg_left hc hA.le
        linarith
      · intro h
        have := mul_lt_mul_of_pos_left h hA
        linarith
    have hRoa' : Ro < v + A * (1 - ((1 - r) * u + r) ^ 2) ↔ (1 - r) * u + r < t := by
      rw [hRo', ← sq_lt_iff hm0 ht0]
      constructor
      · intro h
        by_contra hc
        push Not at hc
        have := mul_le_mul_of_nonneg_left hc hA.le
        linarith
      · intro h
        have := mul_lt_mul_of_pos_left h hA
        linarith
    rw [hRoa, hRoa']
    have hpos : 0 < u * N := by positivity
    have hAμN : 0 < A * μ * N := by positivity
    have hF2 : 0 ≤ r * (u - 1) + (u - t) := by
      have := mul_nonneg hr0 (sub_pos.mpr hu1).le
      linarith
    constructor
    · constructor
      · intro hE0
        by_contra hc
        push Not at hc
        have hF1 : 0 ≤ r * (u - 1) - (u - t) := by linarith
        have h1 : 0 ≤ A * μ * N * ((r * (u - 1) - (u - t)) * (r * (u - 1) + (u - t))) :=
          mul_nonneg hAμN.le (mul_nonneg hF1 hF2)
        have h2 := mul_neg_of_neg_of_pos hE0 hpos
        linarith
      · intro hlt
        have hF1 : r * (u - 1) - (u - t) < 0 := by linarith
        have hF2' : 0 < r * (u - 1) + (u - t) := by
          have := mul_nonneg hr0 (sub_pos.mpr hu1).le
          linarith
        have h1 : A * μ * N * ((r * (u - 1) - (u - t)) * (r * (u - 1) + (u - t))) < 0 :=
          mul_neg_of_pos_of_neg hAμN (mul_neg_of_neg_of_pos hF1 hF2')
        by_contra hc
        push Not at hc
        have h2 := mul_nonneg hc hpos.le
        linarith
    · constructor
      · intro hE0
        by_contra hc
        push Not at hc
        have hF1 : r * (u - 1) - (u - t) ≤ 0 := by linarith
        have h1 : A * μ * N * ((r * (u - 1) - (u - t)) * (r * (u - 1) + (u - t))) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hAμN.le (mul_nonpos_of_nonpos_of_nonneg hF1 hF2)
        have h2 := mul_pos hE0 hpos
        linarith
      · intro hlt
        have hF1 : 0 < r * (u - 1) - (u - t) := by linarith
        have hF2' : 0 < r * (u - 1) + (u - t) := by linarith
        have h1 : 0 < A * μ * N * ((r * (u - 1) - (u - t)) * (r * (u - 1) + (u - t))) :=
          mul_pos hAμN (mul_pos hF1 hF2')
        by_contra hc
        push Not at hc
        have h2 := mul_nonpos_of_nonpos_of_nonneg hc hpos.le
        linarith
  · have hmx : max (v - Ro) 0 = 0 := max_eq_right (by linarith)
    rw [hmx, zero_div, add_zero, Real.sqrt_one] at ht
    subst ht
    have hav : v + A * (1 - ((1 - r) * u + r) ^ 2) < v := by
      have h1 : 1 < ((1 - r) * u + r) ^ 2 := by
        have := (sq_lt_iff zero_le_one hm0).mpr hm1
        simpa using this
      have := mul_pos hA (sub_pos.mpr h1)
      linarith
    have hneg : A * μ / N * (u - 1) ^ 2 - A * μ * (1 - 1) ^ 2 - Ro * (μ * (u - 1) / u) < 0 := by
      have e1 : (A * μ / N * (u - 1) ^ 2 - A * μ * (1 - 1) ^ 2 - Ro * (μ * (u - 1) / u)) * (u * N)
          = A * μ * u * (u - 1) ^ 2 - N * Ro * μ * (u - 1) := by
        field_simp
        try ring
      have hNv : N * v = A * (u ^ 2 - 1) := by rw [hvv]; field_simp
      have hu10 : 0 < u - 1 := by linarith
      have h3 : N * μ * (u - 1) * v < N * μ * (u - 1) * Ro :=
        mul_lt_mul_of_pos_left hRv (by positivity)
      have h4 : A * μ * u * (u - 1) ^ 2 - N * v * μ * (u - 1) = -(A * μ * (u - 1) ^ 2) := by
        rw [hNv]; ring
      have h5 : 0 < A * μ * (u - 1) ^ 2 := by positivity
      have hpos : 0 < u * N := by positivity
      by_contra hc
      push Not at hc
      have h6 := mul_nonneg hc hpos.le
      have h7 : N * v * μ * (u - 1) = N * μ * (u - 1) * v := by ring
      have h8 : N * Ro * μ * (u - 1) = N * μ * (u - 1) * Ro := by ring
      linarith
    constructor
    · exact ⟨fun _ => by linarith, fun _ => hneg⟩
    · constructor
      · intro h; linarith
      · intro h; linarith

lemma b_rel (A μ K v Ro t k : ℝ) (hA : 0 < A) (hμ : 0 < μ) (hK : 0 ≤ K)
    (ht : t = Real.sqrt (1 + max (v - Ro) 0 / A)) (hk : k = Real.sqrt (K / (A * μ))) :
    (K < A * μ * (t - 1) ^ 2 ↔ Ro < v + A * (1 - (1 + k) ^ 2)) ∧
    (0 < K → K ≤ A * μ * (t - 1) ^ 2 → Ro ≤ v + A * (1 - (1 + k) ^ 2)) := by
  have hX0 : 0 ≤ max (v - Ro) 0 := le_max_right _ _
  have ht2 : t ^ 2 = 1 + max (v - Ro) 0 / A := by
    rw [ht]; exact Real.sq_sqrt (by positivity)
  have ht0 : 0 ≤ t := ht ▸ Real.sqrt_nonneg _
  have ht1 : 1 ≤ t := by
    have : 0 ≤ max (v - Ro) 0 / A := by positivity
    nlinarith
  have hk2 : k ^ 2 = K / (A * μ) := by rw [hk]; exact Real.sq_sqrt (by positivity)
  have hk0 : 0 ≤ k := hk ▸ Real.sqrt_nonneg _
  have hKk : K = A * μ * k ^ 2 := by rw [hk2]; field_simp
  have hX : max (v - Ro) 0 = A * (t ^ 2 - 1) := by rw [ht2]; field_simp; ring
  have hAμ : 0 < A * μ := by positivity
  constructor
  · rw [hKk]
    constructor
    · intro h
      have h1 : k ^ 2 < (t - 1) ^ 2 := by
        by_contra hc; push Not at hc; nlinarith
      have h2 : k < t - 1 := by nlinarith
      have h3 : (1 + k) ^ 2 < t ^ 2 := by nlinarith
      have h4 : A * ((1 + k) ^ 2 - 1) < max (v - Ro) 0 := by rw [hX]; nlinarith
      have h5 : 0 ≤ A * ((1 + k) ^ 2 - 1) := by
        have : 0 ≤ (1 + k) ^ 2 - 1 := by nlinarith
        positivity
      rcases lt_max_iff.mp h4 with h6 | h6
      · nlinarith
      · linarith
    · intro h
      have h5 : 0 ≤ A * ((1 + k) ^ 2 - 1) := by
        have : 0 ≤ (1 + k) ^ 2 - 1 := by nlinarith
        positivity
      have h4 : A * ((1 + k) ^ 2 - 1) < max (v - Ro) 0 :=
        lt_max_iff.mpr (Or.inl (by nlinarith))
      rw [hX] at h4
      have h3 : (1 + k) ^ 2 < t ^ 2 := by
        by_contra hc; push Not at hc; nlinarith
      have h2 : k < t - 1 := by nlinarith
      have h1 : k ^ 2 < (t - 1) ^ 2 := by nlinarith
      nlinarith
  · intro hKp hle
    rw [hKk] at hKp hle
    have hkp : 0 < k := by
      rcases hk0.lt_or_eq with h | h
      · exact h
      · rw [← h] at hKp; simp at hKp
    have h1 : k ^ 2 ≤ (t - 1) ^ 2 := by
      by_contra hc; push Not at hc; nlinarith
    have h2 : k ≤ t - 1 := by nlinarith
    have h3 : (1 + k) ^ 2 ≤ t ^ 2 := by nlinarith
    have h5 : 0 < A * ((1 + k) ^ 2 - 1) := by
      have : 0 < (1 + k) ^ 2 - 1 := by nlinarith
      positivity
    have h4 : A * ((1 + k) ^ 2 - 1) ≤ max (v - Ro) 0 := by rw [hX]; nlinarith
    rcases le_max_iff.mp h4 with h6 | h6
    · nlinarith
    · linarith

lemma decide_core (G Go K L Ro a b N : ℝ) (hG : 0 < G) (hGo0 : 0 ≤ Go) (hK : 0 ≤ K)
    (hRo : 0 ≤ Ro) (hL : 0 ≤ L) (hGoG : Go ≤ G) (hN : 0 < N)
    (B1' : K < Go ↔ Ro < b) (B1 : 0 < K → K ≤ Go → Ro ≤ b)
    (B2a : G - Go - Ro * L < 0 ↔ a < Ro) (B2b : 0 < G - Go - Ro * L ↔ Ro < a)
    (pt : ℝ → ℝ)
    (hpt : ∀ w, 0 ≤ w → pt w = if max K Go ≤ w * G then N * ((1 - w) * G - Ro * L) else 0) :
    ((if max K Go ≤ G - Ro * L then max K Go / G else 0) ∈ Set.Icc (0:ℝ) 1 ∧
      ∀ t ∈ Set.Icc (0:ℝ) 1, pt t ≤ pt (if max K Go ≤ G - Ro * L then max K Go / G else 0)) ∧
    (∀ w ∈ Set.Icc (0:ℝ) 1, (∀ t ∈ Set.Icc (0:ℝ) 1, pt t ≤ pt w) → Ro ≠ a → Ro ≠ b →
      ((¬ (max K Go ≤ w * G) ∧ K ≤ Go) ↔ (a < Ro ∧ Ro < b))) ∧
    (Ro ≠ b → ((¬ (max K Go ≤ (if max K Go ≤ G - Ro * L then max K Go / G else 0) * G) ∧
      K ≤ Go) ↔ (a < Ro ∧ Ro < b))) := by
  have hM0 : 0 ≤ max K Go := le_trans hK (le_max_left _ _)
  have hMK := le_max_left K Go
  have hMGo := le_max_right K Go
  have hRL : 0 ≤ Ro * L := mul_nonneg hRo hL
  have hws : max K Go / G * G = max K Go := div_mul_cancel₀ _ hG.ne'
  have e1 : (1 - max K Go / G) * G = G - max K Go := by rw [sub_mul, hws, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · split_ifs with hc
    · refine ⟨⟨div_nonneg hM0 hG.le, (div_le_one hG).mpr (by linarith)⟩, ?_⟩
      intro t ht
      rw [hpt t ht.1, hpt _ (div_nonneg hM0 hG.le), if_pos (le_of_eq hws.symm), e1]
      split_ifs with h2
      · have : (1 - t) * G = G - t * G := by ring
        apply mul_le_mul_of_nonneg_left _ hN.le
        linarith
      · exact mul_nonneg hN.le (by linarith)
    · refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
      intro t ht
      have htG : 0 ≤ t * G := mul_nonneg ht.1 hG.le
      rw [hpt t ht.1, hpt 0 le_rfl, zero_mul]
      split_ifs with h1 h2 h2
      · apply mul_le_mul_of_nonneg_left _ hN.le
        nlinarith
      · have : (1 - t) * G - Ro * L < 0 := by nlinarith
        nlinarith
      · exact absurd (h2.trans htG) h1
      · exact le_rfl
  · intro w hw hopt ha hb
    have hpw := hpt w hw.1
    have hwG : 0 ≤ w * G := mul_nonneg hw.1 hG.le
    constructor
    · rintro ⟨hc, hKGo⟩
      have hmax : max K Go = Go := max_eq_right hKGo
      rw [hmax, not_le] at hc
      have hb' : Ro < b := by
        rcases hKGo.lt_or_eq with h | h
        · exact B1'.mp h
        · exact lt_of_le_of_ne (B1 (by linarith) hKGo) hb
      refine ⟨?_, hb'⟩
      by_contra hna
      push Not at hna
      have hlt : Ro < a := lt_of_le_of_ne hna ha
      have hpos := B2b.mpr hlt
      have ht : Go / G ∈ Set.Icc (0:ℝ) 1 := ⟨div_nonneg hGo0 hG.le, (div_le_one hG).mpr hGoG⟩
      have h1 := hopt _ ht
      have e2 : (1 - Go / G) * G = G - Go := by rw [sub_mul, div_mul_cancel₀ _ hG.ne', one_mul]
      have hGoG' : Go / G * G = Go := div_mul_cancel₀ _ hG.ne'
      rw [hpt _ ht.1, hpw, hmax, if_neg (not_le.mpr hc), if_pos (le_of_eq hGoG'.symm), e2] at h1
      have := mul_pos hN hpos
      linarith
    · rintro ⟨hlt, hbt⟩
      have hKGo := B1'.mpr hbt
      have hmax : max K Go = Go := max_eq_right hKGo.le
      have hneg := B2a.mpr hlt
      refine ⟨fun hc => ?_, hKGo.le⟩
      rw [hmax] at hc
      have h0 := hopt 0 ⟨le_rfl, zero_le_one⟩
      rw [hpt 0 le_rfl, hpw, hmax, if_pos hc, zero_mul, if_neg (not_le.mpr (by linarith))] at h0
      have : (1 - w) * G - Ro * L < 0 := by nlinarith
      have := mul_neg_of_pos_of_neg hN this
      linarith
  · intro hb
    split_ifs with hc
    · rw [hws]
      constructor
      · rintro ⟨h, _⟩; exact absurd le_rfl h
      · rintro ⟨hlt, hbt⟩
        have hKGo := B1'.mpr hbt
        have hmax : max K Go = Go := max_eq_right hKGo.le
        have hneg := B2a.mpr hlt
        rw [hmax] at hc
        linarith
    · rw [zero_mul]
      constructor
      · rintro ⟨h, hKGo⟩
        have hmax : max K Go = Go := max_eq_right hKGo
        rw [hmax, not_le] at h
        rw [hmax, not_le] at hc
        have hb' : Ro < b := by
          rcases hKGo.lt_or_eq with h' | h'
          · exact B1'.mp h'
          · exact lt_of_le_of_ne (B1 (by linarith) hKGo) hb
        exact ⟨B2a.mp (by linarith), hb'⟩
      · rintro ⟨hlt, hbt⟩
        have hKGo := B1'.mpr hbt
        exact ⟨not_le.mpr (by linarith), hKGo.le⟩

end PL3Aux

namespace PL3Aux

open PlatformLeakage.Perfect

lemma std_facts {P : Params} (hP : P.Std) (j : PType) :
    1 ≤ P.N j ∧ 0 < P.v j ∧ 0 ≤ P.K j ∧ 0 < P.mu ∧ 0 < P.c * P.phi ∧ 0 ≤ P.Ro := by
  obtain ⟨h1, _, h3, h4, h5, h6, _⟩ := hP
  refine ⟨(h1 j).1, (h1 j).2.1, (h1 j).2.2, h3, ?_, h6⟩
  unfold Params.phi
  have : 0 < (1 + P.cs2) / 2 := by linarith
  exact mul_pos h4 this

lemma cphi_ne {P : Params} (hP : P.Std) : P.c ≠ 0 ∧ P.phi ≠ 0 := by
  obtain ⟨_, _, _, h4, h5, _, _⟩ := hP
  refine ⟨h4.ne', ?_⟩
  unfold Params.phi
  have : 0 < (1 + P.cs2) / 2 := by linarith
  exact this.ne'

lemma onValue_greatest {P : Params} (hP : P.Std) (j : PType) (n : ℕ) (hn : 1 ≤ n) :
    IsGreatest ((fun ζ : ℝ => ζ * demandP P j n ζ) '' Set.Ici 0)
      (P.c * P.phi * P.mu / n * (Real.sqrt (1 + (n:ℝ) * P.v j / (P.c * P.phi)) - 1) ^ 2) := by
  obtain ⟨_, hv, _, hμ, hA, _⟩ := std_facts hP j
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  set u := Real.sqrt (1 + (n:ℝ) * P.v j / (P.c * P.phi)) with hu
  have hu2 : u ^ 2 = 1 + (n:ℝ) * P.v j / (P.c * P.phi) := Real.sq_sqrt (by positivity)
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu1 : 1 < u := by
    have : 0 < (n:ℝ) * P.v j / (P.c * P.phi) := by positivity
    nlinarith
  have hvv : P.v j = P.c * P.phi * (u ^ 2 - 1) / n := by
    obtain ⟨hc0, hp0⟩ := cphi_ne hP
    rw [hu2]; field_simp; try ring
  unfold demandP
  rw [hvv]
  exact rev_greatest _ _ _ _ hA hμ hn' hu1

lemma onValue_zero (P : Params) (j : PType) : onValue P j 0 = 0 := by
  unfold onValue demandP
  simp only [Nat.cast_zero, zero_mul, zero_div, mul_zero, add_zero]
  rw [Set.Nonempty.image_const Set.nonempty_Ici]
  exact csSup_singleton 0

lemma demandP_nonneg {P : Params} (hP : P.Std) (j : PType) (n : ℕ) (ζ : ℝ) :
    0 ≤ demandP P j n ζ := by
  obtain ⟨_, _, _, hμ, hA, _⟩ := std_facts hP j
  unfold demandP
  have h0 : 0 ≤ (n:ℝ) * max (P.v j - ζ) 0 := mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)
  exact mul_nonneg hμ.le (div_nonneg h0 (by linarith))

lemma demandP_mono {P : Params} (hP : P.Std) (j : PType) {n m : ℕ} (h : n ≤ m) (ζ : ℝ) :
    demandP P j n ζ ≤ demandP P j m ζ := by
  obtain ⟨_, _, _, hμ, hA, _⟩ := std_facts hP j
  unfold demandP
  apply mul_le_mul_of_nonneg_left _ hμ.le
  apply frac_mono hA (mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _))
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) (le_max_right _ _)

lemma onValue_le {P : Params} (hP : P.Std) (j : PType) (n : ℕ) (hn : n ≤ P.N j) :
    onValue P j n ≤ onValue P j (P.N j) := by
  have hg := onValue_greatest hP j (P.N j) (std_facts hP j).1
  have hval : onValue P j (P.N j) = _ := hg.csSup_eq
  rw [hval]
  unfold onValue
  apply csSup_le (Set.nonempty_Ici.image _)
  rintro _ ⟨ζ, hζ, rfl⟩
  exact (mul_le_mul_of_nonneg_left (demandP_mono hP j hn ζ) hζ).trans (hg.2 ⟨ζ, hζ, rfl⟩)

lemma onValue_pos {P : Params} (hP : P.Std) (j : PType) : 0 < onValue P j (P.N j) := by
  obtain ⟨hN1, hv, _, hμ, hA, _⟩ := std_facts hP j
  have hval : onValue P j (P.N j) = _ := (onValue_greatest hP j (P.N j) hN1).csSup_eq
  rw [hval]
  have hn' : (0:ℝ) < P.N j := by exact_mod_cast hN1
  have hu1 : 1 < Real.sqrt (1 + (P.N j:ℝ) * P.v j / (P.c * P.phi)) := by
    rw [Real.lt_sqrt zero_le_one]
    have : 0 < (P.N j:ℝ) * P.v j / (P.c * P.phi) := by positivity
    linarith
  exact mul_pos (div_pos (mul_pos hA hμ) hn') (pow_pos (by linarith) 2)

lemma fee_facts {P : Params} (hP : P.Std) (j : PType) :
    feeP P j (P.N j) * demandP P j (P.N j) (feeP P j (P.N j)) = onValue P j (P.N j) ∧
    demandP P j (P.N j) (feeP P j (P.N j)) =
      P.mu * (Real.sqrt (1 + (P.N j:ℝ) * P.v j / (P.c * P.phi)) - 1) /
        Real.sqrt (1 + (P.N j:ℝ) * P.v j / (P.c * P.phi)) := by
  obtain ⟨hN1, hv, _, hμ, hA, _⟩ := std_facts hP j
  have hg := onValue_greatest hP j (P.N j) hN1
  have hval : onValue P j (P.N j) = _ := hg.csSup_eq
  obtain ⟨⟨ζ0, hζ0, heq⟩, hub⟩ := hg
  simp only at heq
  have hex : ∃ ζ : ℝ, 0 ≤ ζ ∧ ∀ ζ' : ℝ, 0 ≤ ζ' →
      ζ' * demandP P j (P.N j) ζ' ≤ ζ * demandP P j (P.N j) ζ :=
    ⟨ζ0, hζ0, fun ζ' h' => by rw [heq]; exact hub ⟨ζ', h', rfl⟩⟩
  have hs : 0 ≤ feeP P j (P.N j) ∧ ∀ ζ' : ℝ, 0 ≤ ζ' →
      ζ' * demandP P j (P.N j) ζ' ≤ feeP P j (P.N j) * demandP P j (P.N j) (feeP P j (P.N j)) :=
    Classical.epsilon_spec hex
  obtain ⟨hf0, hfmax⟩ := hs
  have hle := hub ⟨feeP P j (P.N j), hf0, rfl⟩
  have hge := hfmax ζ0 hζ0
  rw [heq] at hge
  refine ⟨by rw [hval]; exact le_antisymm hle hge, ?_⟩
  have hn' : (0:ℝ) < P.N j := by exact_mod_cast hN1
  set u := Real.sqrt (1 + (P.N j:ℝ) * P.v j / (P.c * P.phi)) with hu
  have hu2 : u ^ 2 = 1 + (P.N j:ℝ) * P.v j / (P.c * P.phi) := Real.sq_sqrt (by positivity)
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu1 : 1 < u := by
    have : 0 < (P.N j:ℝ) * P.v j / (P.c * P.phi) := by positivity
    nlinarith
  have hvv : P.v j = P.c * P.phi * (u ^ 2 - 1) / (P.N j) := by
    obtain ⟨hc0, hp0⟩ := cphi_ne hP
    rw [hu2]; field_simp; try ring
  unfold demandP at hge ⊢
  rw [hvv] at hge ⊢
  exact rev_eq _ _ _ _ _ hA hμ hn' hu1 hf0 hge

lemma offValue_greatest {P : Params} (hP : P.Std) (j : PType) :
    IsGreatest ((fun q : ℝ => q * demandO P j q) '' Set.Ici 0)
      (P.c * P.phi * P.mu * (Real.sqrt (1 + max (P.v j - P.Ro) 0 / (P.c * P.phi)) - 1) ^ 2) := by
  obtain ⟨_, hv, _, hμ, hA, _⟩ := std_facts hP j
  rcases le_or_gt (P.v j - P.Ro) 0 with h | h
  · rw [max_eq_right h]
    simp only [zero_div, add_zero, Real.sqrt_one, sub_self]
    refine ⟨⟨0, Set.mem_Ici.mpr le_rfl, by simp⟩, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    have hq' : (0:ℝ) ≤ q := hq
    have : P.v j - q - P.Ro ≤ 0 := by linarith
    simp [demandO, max_eq_right this]
  · rw [max_eq_left h.le]
    set u := Real.sqrt (1 + (P.v j - P.Ro) / (P.c * P.phi)) with hu
    have hd : 0 < (P.v j - P.Ro) / (P.c * P.phi) := div_pos h hA
    have hu2 : u ^ 2 = 1 + (P.v j - P.Ro) / (P.c * P.phi) := Real.sq_sqrt (by linarith)
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    have hu1 : 1 < u := by nlinarith
    have hw : ∀ q : ℝ, P.v j - q - P.Ro = P.c * P.phi * (u ^ 2 - 1) / 1 - q := by
      intro q
      obtain ⟨hc0, hp0⟩ := cphi_ne hP
      rw [hu2]; field_simp; try ring
    have hfun : (fun q : ℝ => q * demandO P j q) = (fun ζ : ℝ => ζ * (P.mu *
        ((1:ℝ) * max (P.c * P.phi * (u ^ 2 - 1) / 1 - ζ) 0 /
          (P.c * P.phi + (1:ℝ) * max (P.c * P.phi * (u ^ 2 - 1) / 1 - ζ) 0)))) := by
      funext q
      simp only [demandO, hw q, one_mul]
    rw [hfun, show P.c * P.phi * P.mu * (u - 1) ^ 2 = P.c * P.phi * P.mu / 1 * (u - 1) ^ 2 by ring]
    exact rev_greatest _ _ _ _ hA hμ one_pos hu1

lemma offValue_le {P : Params} (hP : P.Std) (j : PType) :
    offValue P j ≤ onValue P j (P.N j) := by
  obtain ⟨hN1, hv, _, hμ, hA, hRo⟩ := std_facts hP j
  have hg := onValue_greatest hP j (P.N j) hN1
  have hval : onValue P j (P.N j) = _ := hg.csSup_eq
  rw [hval]
  unfold offValue
  apply csSup_le (Set.nonempty_Ici.image _)
  rintro _ ⟨q, hq, rfl⟩
  refine le_trans ?_ (hg.2 ⟨q, hq, rfl⟩)
  have hq' : (0:ℝ) ≤ q := hq
  apply mul_le_mul_of_nonneg_left _ hq'
  unfold demandO demandP
  apply mul_le_mul_of_nonneg_left _ hμ.le
  have h1 : max (P.v j - q - P.Ro) 0 ≤ max (P.v j - q) 0 := max_le_max (by linarith) le_rfl
  have h2 : max (P.v j - q) 0 ≤ (P.N j : ℝ) * max (P.v j - q) 0 := by
    have : (1:ℝ) ≤ P.N j := by exact_mod_cast hN1
    have := le_max_right (P.v j - q) 0
    nlinarith
  exact frac_mono hA (le_max_right _ _) (h1.trans h2)

lemma offValue_eq {P : Params} (hP : P.Std) (j : PType) : offValue P j =
    P.c * P.phi * P.mu * (Real.sqrt (1 + max (P.v j - P.Ro) 0 / (P.c * P.phi)) - 1) ^ 2 :=
  (offValue_greatest hP j).csSup_eq

lemma Khat_eq {P : Params} (hP : P.Std) (j : PType) : Khat P j = max (P.K j) (offValue P j) := by
  rw [offValue_eq hP j]
  unfold Khat g2
  congr 1
  simp only [one_mul, div_one]
  ring

lemma omegaStar_eq {P : Params} (hP : P.Std) (j : PType) :
    omegaStar P j = if Khat P j ≤ onValue P j (P.N j) - P.Ro * demandP P j (P.N j) (feeP P j (P.N j))
      then Khat P j / onValue P j (P.N j) else 0 := by
  obtain ⟨hN1, hv, _, hμ, hA, _⟩ := std_facts hP j
  have hval : onValue P j (P.N j) = _ := (onValue_greatest hP j (P.N j) hN1).csSup_eq
  rw [hval, (fee_facts hP j).2]
  have hn' : (0:ℝ) < P.N j := by exact_mod_cast hN1
  unfold omegaStar g2
  set u := Real.sqrt (1 + (P.N j:ℝ) * P.v j / (P.c * P.phi)) with hu
  have hu2 : u ^ 2 = 1 + (P.N j:ℝ) * P.v j / (P.c * P.phi) := Real.sq_sqrt (by positivity)
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu1 : 1 < u := by
    have : 0 < (P.N j:ℝ) * P.v j / (P.c * P.phi) := by positivity
    nlinarith
  have hsq : Real.sqrt (P.c * P.phi / (P.c * P.phi + (P.N j:ℝ) * P.v j)) = 1 / u := by
    have : P.c * P.phi / (P.c * P.phi + (P.N j:ℝ) * P.v j) = (1 / u) ^ 2 := by
      obtain ⟨hc0, hp0⟩ := cphi_ne hP
      rw [div_pow, one_pow, hu2]
      field_simp
      try ring
    rw [this]
    exact Real.sqrt_sq (by positivity)
  rw [hsq]
  have e1 : P.c * P.mu * P.phi / (P.N j:ℝ) * (u - 1) ^ 2 = P.c * P.phi * P.mu / (P.N j:ℝ) * (u - 1) ^ 2 := by ring
  have hu0' : u ≠ 0 := by positivity
  have e2 : P.mu * P.Ro * (1 - 1 / u) = P.Ro * (P.mu * (u - 1) / u) := by
    field_simp
  rw [e1, e2]

lemma isPartEq_top {P : Params} (hP : P.Std) (j : PType) {ω : ℝ}
    (hc : max (P.K j) (offValue P j) ≤ ω * onValue P j (P.N j)) :
    IsPartEq P j ω (P.N j) 0 := by
  unfold IsPartEq Uo Up
  refine ⟨by simp, fun _ => ?_, fun h => absurd h (lt_irrefl 0), fun h => by simp at h⟩
  have := le_max_left (P.K j) (offValue P j)
  have := le_max_right (P.K j) (offValue P j)
  exact max_le (by linarith) (by linarith)

lemma isPartEq_np_pos {P : Params} (hP : P.Std) (j : PType) {ω : ℝ} (hω : 0 ≤ ω) {Np No : ℕ}
    (h : IsPartEq P j ω Np No) (hNp : 0 < Np) :
    max (P.K j) (offValue P j) ≤ ω * onValue P j (P.N j) := by
  obtain ⟨hsum, h1, _, _⟩ := h
  have h1 := h1 hNp
  unfold Uo Up at h1
  have hle : onValue P j Np ≤ onValue P j (P.N j) := onValue_le hP j Np (by omega)
  have : ω * onValue P j Np ≤ ω * onValue P j (P.N j) := mul_le_mul_of_nonneg_left hle hω
  have := le_max_left (offValue P j - P.K j) 0
  have := le_max_right (offValue P j - P.K j) 0
  exact max_le (by linarith) (by linarith)

lemma offValue_nonneg {P : Params} (hP : P.Std) (j : PType) : 0 ≤ offValue P j := by
  rw [offValue_eq hP j]
  obtain ⟨_, _, _, hμ, hA, _⟩ := std_facts hP j
  positivity

lemma isPartEq_bottom {P : Params} (hP : P.Std) (j : PType) {ω : ℝ} (hω : 0 ≤ ω)
    (hc : ¬ max (P.K j) (offValue P j) ≤ ω * onValue P j (P.N j)) (hK : P.K j ≤ offValue P j) :
    IsPartEq P j ω 0 (P.N j) := by
  have hmax : max (P.K j) (offValue P j) = offValue P j := max_eq_right hK
  rw [hmax, not_le] at hc
  have hle : onValue P j (0 + 1) ≤ onValue P j (P.N j) :=
    onValue_le hP j _ (by have := (std_facts hP j).1; omega)
  have h1 : ω * onValue P j (0 + 1) ≤ ω * onValue P j (P.N j) := mul_le_mul_of_nonneg_left hle hω
  have h0 := offValue_nonneg hP j
  unfold IsPartEq Uo Up
  refine ⟨by simp, fun h => absurd h (lt_irrefl 0), fun _ => ⟨?_, ?_⟩, fun h => by simp at h⟩
  · rw [onValue_zero, mul_zero]
    exact max_le (by linarith) (by linarith)
  · linarith

lemma isPartEq_none {P : Params} (hP : P.Std) (j : PType) {ω : ℝ} (hω : 0 ≤ ω)
    (hc : ¬ max (P.K j) (offValue P j) ≤ ω * onValue P j (P.N j)) (hK : offValue P j < P.K j) :
    IsPartEq P j ω 0 0 := by
  have hmax : max (P.K j) (offValue P j) = P.K j := max_eq_left hK.le
  rw [hmax, not_le] at hc
  have hle : onValue P j (0 + 1) ≤ onValue P j (P.N j) :=
    onValue_le hP j _ (by have := (std_facts hP j).1; omega)
  have h1 : ω * onValue P j (0 + 1) ≤ ω * onValue P j (P.N j) := mul_le_mul_of_nonneg_left hle hω
  unfold IsPartEq Uo Up
  refine ⟨by simp, fun h => absurd h (lt_irrefl 0), fun h => absurd h (lt_irrefl 0),
    fun _ => ⟨by linarith, by linarith⟩⟩

lemma sel_iff {P : Params} (hP : P.Std) (j : PType) {ω : ℝ} (hω : 0 ≤ ω) {Np No : ℕ}
    (hs : IsSelectedEq P j ω Np No) :
    0 < No ↔ (¬ (max (P.K j) (offValue P j) ≤ ω * onValue P j (P.N j)) ∧
      P.K j ≤ offValue P j) := by
  obtain ⟨heq, hmax⟩ := hs
  constructor
  · intro hNo
    refine ⟨fun hc => ?_, ?_⟩
    · have := hmax _ _ (isPartEq_top hP j hc)
      have := heq.1
      omega
    · have h3 := (heq.2.2.1 hNo).1
      unfold Uo at h3
      have := le_max_right (Up P j ω Np) 0
      linarith
  · rintro ⟨hc, hK⟩
    have hNp : Np = 0 := by
      by_contra h
      exact hc (isPartEq_np_pos hP j hω heq (Nat.pos_of_ne_zero h))
    by_contra hNo
    have hNo0 : No = 0 := by omega
    have hN1 := (std_facts hP j).1
    have := (heq.2.2.2 (by rw [hNp, hNo0]; omega)).2
    unfold Uo at this
    linarith

lemma sel_exists {P : Params} (hP : P.Std) (j : PType) {ω : ℝ} (hω : 0 ≤ ω) :
    ∃ Np No : ℕ, IsSelectedEq P j ω Np No := by
  by_cases hc : max (P.K j) (offValue P j) ≤ ω * onValue P j (P.N j)
  · exact ⟨P.N j, 0, isPartEq_top hP j hc, fun Np' No' h => by have := h.1; omega⟩
  · by_cases hK : P.K j ≤ offValue P j
    · refine ⟨0, P.N j, isPartEq_bottom hP j hω hc hK, fun Np' No' h => ?_⟩
      by_contra h'
      exact hc (isPartEq_np_pos hP j hω h (by omega))
    · push Not at hK
      refine ⟨0, 0, isPartEq_none hP j hω hc hK, fun Np' No' h => ?_⟩
      by_contra h'
      exact hc (isPartEq_np_pos hP j hω h (by omega))

lemma selNp_eq {P : Params} (hP : P.Std) (j : PType) {ω : ℝ} (hω : 0 ≤ ω) :
    selNp P j ω = if max (P.K j) (offValue P j) ≤ ω * onValue P j (P.N j) then P.N j else 0 := by
  classical
  unfold selNp
  split_ifs with hc
  · exact Nat.findGreatest_eq ⟨0, isPartEq_top hP j hc⟩
  · by_contra hne
    obtain ⟨no, hno⟩ := Nat.findGreatest_of_ne_zero rfl hne
    exact hc (isPartEq_np_pos hP j hω hno (Nat.pos_of_ne_zero hne))

lemma profitTerm_eq {P : Params} (hP : P.Std) (j : PType) (ω : ℝ) (hω : 0 ≤ ω) :
    profitTerm P j ω = if max (P.K j) (offValue P j) ≤ ω * onValue P j (P.N j) then
      (P.N j : ℝ) * ((1 - ω) * onValue P j (P.N j) -
        P.Ro * demandP P j (P.N j) (feeP P j (P.N j))) else 0 := by
  unfold profitTerm
  rw [selNp_eq hP j hω]
  split_ifs with hc
  · rw [← (fee_facts hP j).1]
    ring
  · simp

lemma B_facts {P : Params} (hP : P.Std) (j : PType) :
    (P.K j < offValue P j ↔ P.Ro < leakHi P j) ∧
    (0 < P.K j → P.K j ≤ offValue P j → P.Ro ≤ leakHi P j) ∧
    (onValue P j (P.N j) - offValue P j - P.Ro * demandP P j (P.N j) (feeP P j (P.N j)) < 0 ↔
      leakLo P j < P.Ro) ∧
    (0 < onValue P j (P.N j) - offValue P j - P.Ro * demandP P j (P.N j) (feeP P j (P.N j)) ↔
      P.Ro < leakLo P j) := by
  obtain ⟨hN1, hv, hK, hμ, hA, hRo⟩ := std_facts hP j
  have hb := b_rel (P.c * P.phi) P.mu (P.K j) (P.v j) P.Ro _ _ hA hμ hK rfl rfl
  have hN1' : (1:ℝ) ≤ P.N j := by exact_mod_cast hN1
  have hh := h_sign (P.c * P.phi) P.mu (P.N j) (P.v j) P.Ro _ _ _ hA hμ hN1' hv hRo rfl rfl rfl
  have hval : onValue P j (P.N j) = _ := (onValue_greatest hP j (P.N j) hN1).csSup_eq
  rw [offValue_eq hP j, hval, (fee_facts hP j).2]
  exact ⟨hb.1, hb.2, hh.1, hh.2⟩

end PL3Aux

open PlatformLeakage.Perfect in
theorem solution (P : Params) (hP : P.Std) :
    (∃ ω : PType → ℝ, IsOptimalPayout P ω) ∧
    (∀ ω : PType → ℝ, IsOptimalPayout P ω → ∀ j : PType,
      (∃ Np No : ℕ, IsSelectedEq P j (ω j) Np No) ∧
      ∀ Np No : ℕ, IsSelectedEq P j (ω j) Np No → P.Ro ≠ leakLo P j → P.Ro ≠ leakHi P j →
        (0 < No ↔ P.Ro ∈ Set.Ioo (leakLo P j) (leakHi P j))) ∧
    (∀ j : PType, ∀ Np No : ℕ, IsSelectedEq P j (omegaStar P j) Np No → P.Ro ≠ leakHi P j →
        (0 < No ↔ P.Ro ∈ Set.Ioo (leakLo P j) (leakHi P j))) := by
  have D := fun j : PType =>
    PL3Aux.decide_core (onValue P j (P.N j)) (offValue P j) (P.K j)
      (demandP P j (P.N j) (feeP P j (P.N j))) P.Ro (leakLo P j) (leakHi P j) (P.N j)
      (PL3Aux.onValue_pos hP j) (PL3Aux.offValue_nonneg hP j) (PL3Aux.std_facts hP j).2.2.1
      (PL3Aux.std_facts hP j).2.2.2.2.2 (PL3Aux.demandP_nonneg hP j _ _) (PL3Aux.offValue_le hP j)
      (by exact_mod_cast (PL3Aux.std_facts hP j).1)
      (PL3Aux.B_facts hP j).1 (PL3Aux.B_facts hP j).2.1 (PL3Aux.B_facts hP j).2.2.1
      (PL3Aux.B_facts hP j).2.2.2 (profitTerm P j) (fun w hw => PL3Aux.profitTerm_eq hP j w hw)
  have hws : ∀ j, omegaStar P j = if max (P.K j) (offValue P j) ≤ onValue P j (P.N j) -
      P.Ro * demandP P j (P.N j) (feeP P j (P.N j))
      then max (P.K j) (offValue P j) / onValue P j (P.N j) else 0 := by
    intro j
    rw [PL3Aux.omegaStar_eq hP j, PL3Aux.Khat_eq hP j]
  refine ⟨⟨omegaStar P, ?_⟩, ?_, ?_⟩
  · refine ⟨fun j => by rw [hws j]; exact (D j).1.1, fun ω' hω' => ?_⟩
    unfold profit
    have h1 := (D PType.h).1.2 _ (hω' PType.h)
    have h2 := (D PType.l).1.2 _ (hω' PType.l)
    rw [← hws] at h1 h2
    exact add_le_add h1 h2
  · intro ω hω j
    have hwj : ω j ∈ Set.Icc (0:ℝ) 1 := hω.1 j
    have hopt : ∀ t ∈ Set.Icc (0:ℝ) 1, profitTerm P j t ≤ profitTerm P j (ω j) := by
      intro t ht
      have hupd : ∀ k, Function.update ω j t k ∈ Set.Icc (0:ℝ) 1 := by
        intro k
        by_cases hk : k = j
        · subst hk; simpa using ht
        · simpa [hk] using hω.1 k
      have := hω.2 _ hupd
      cases j <;> simp [profit, Function.update_apply] at this <;> linarith
    refine ⟨PL3Aux.sel_exists hP j hwj.1, fun Np No hs ha hb => ?_⟩
    rw [PL3Aux.sel_iff hP j hwj.1 hs, Set.mem_Ioo]
    exact (D j).2.1 (ω j) hwj hopt ha hb
  · intro j Np No hs hb
    have h0 : 0 ≤ omegaStar P j := by rw [hws j]; exact (D j).1.1.1
    rw [PL3Aux.sel_iff hP j h0 hs, Set.mem_Ioo, hws j]
    exact (D j).2.2 hb
