-- Prove2me | solution 1 for RecallTesting.Duopoly.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T01:18:25.361483+00:00
-- url     : https://prove2.me/submissions/8576035e-cfba-452b-b2a8-d2aa20fa51bc

import Mathlib
import Definitions.Def_RecallTesting_Duopoly_Model

set_option autoImplicit false

namespace RecallTestingAux

open RecallTesting.Duopoly MeasureTheory

lemma tie_null (q p q' p' : ℝ) (h : q ≠ q') :
    volume {ϕ : ℝ | ϕ ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ ϕ * q - p ∧ ϕ * q - p = ϕ * q' - p'} = 0 := by
  apply measure_mono_null (t := {(p - p') / (q - q')}) _ (measure_singleton _)
  intro ϕ hϕ
  obtain ⟨-, -, he⟩ := hϕ
  simp only [Set.mem_singleton_iff]
  have hne : q - q' ≠ 0 := sub_ne_zero.2 h
  rw [eq_div_iff hne]
  linear_combination he

lemma demand_hi (q p q' p' s : ℝ) (hq : q' < q) (hq0 : 0 < q)
    (hs : p - p' = (q - q') * s) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hps : p ≤ q * s) :
    demand q p q' p' = 1 - s := by
  have hset : {ϕ : ℝ | ϕ ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ ϕ * q - p ∧ ϕ * q' - p' < ϕ * q - p}
      = Set.Ioc s 1 := by
    ext ϕ
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_Ioc]
    have e1 : ϕ * q - p - (ϕ * q' - p') = (q - q') * (ϕ - s) := by
      linear_combination (-1 : ℝ) * hs
    constructor
    · rintro ⟨⟨_, h1⟩, _, h3⟩
      refine ⟨?_, h1⟩
      by_contra hc
      push Not at hc
      nlinarith [mul_nonneg (sub_nonneg.2 hq.le) (sub_nonneg.2 hc)]
    · rintro ⟨h1, h2⟩
      refine ⟨⟨by linarith, h2⟩, ?_, ?_⟩
      · nlinarith [mul_nonneg hq0.le (sub_nonneg.2 h1.le)]
      · nlinarith [mul_pos (sub_pos.2 hq) (sub_pos.2 h1)]
  unfold demand
  rw [hset, tie_null q p q' p' hq.ne', Real.volume_Ioc]
  simp [ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 - s)]

lemma demand_lo (q p q' p' s t : ℝ) (hq : q < q') (hq0 : 0 < q)
    (hs : p' - p = (q' - q) * s) (ht : p = q * t) (ht0 : 0 ≤ t) (hts : t ≤ s) (hs1 : s ≤ 1) :
    demand q p q' p' = s - t := by
  have hset : {ϕ : ℝ | ϕ ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ ϕ * q - p ∧ ϕ * q' - p' < ϕ * q - p}
      = Set.Ico t s := by
    ext ϕ
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_Ico]
    have e1 : ϕ * q' - p' - (ϕ * q - p) = (q' - q) * (ϕ - s) := by
      linear_combination (-1 : ℝ) * hs
    have e2 : ϕ * q - p = q * (ϕ - t) := by rw [ht]; ring
    constructor
    · rintro ⟨⟨_, _⟩, h2, h3⟩
      refine ⟨?_, ?_⟩
      · by_contra hc
        push Not at hc
        nlinarith [mul_pos hq0 (sub_pos.2 hc)]
      · by_contra hc
        push Not at hc
        nlinarith [mul_nonneg (sub_nonneg.2 hq.le) (sub_nonneg.2 hc)]
    · rintro ⟨h1, h2⟩
      refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩
      · nlinarith [mul_nonneg hq0.le (sub_nonneg.2 h1)]
      · nlinarith [mul_pos (sub_pos.2 hq) (sub_pos.2 h2)]
  unfold demand
  rw [hset, tie_null q p q' p' hq.ne, Real.volume_Ico]
  simp [ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ s - t)]

lemma pp_hi (q q' : ℝ) (h0 : 0 < q') (h : q' < q) :
    periodProfit q q' = 4 * q ^ 2 * (q - q') / (4 * q - q') ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hD : 0 < 4 * q - q' := by linarith
  have hDne : 4 * q - q' ≠ 0 := hD.ne'
  have e1 : eqPrice q q' = 2 * q * (q - q') / (4 * q - q') := by
    rw [eqPrice, if_pos h]
  have e2 : eqPrice q' q = q' * (q - q') / (4 * q - q') := by
    rw [eqPrice, if_neg (not_lt.2 h.le), if_pos h]
  have hs : 2 * q * (q - q') / (4 * q - q') - q' * (q - q') / (4 * q - q')
      = (q - q') * ((2 * q - q') / (4 * q - q')) := by
    field_simp <;> ring
  have hs0 : 0 ≤ (2 * q - q') / (4 * q - q') := div_nonneg (by linarith) hD.le
  have hs1 : (2 * q - q') / (4 * q - q') ≤ 1 := (div_le_one hD).2 (by linarith)
  have hps' : q * ((2 * q - q') / (4 * q - q')) - 2 * q * (q - q') / (4 * q - q')
      = q * q' / (4 * q - q') := by
    field_simp <;> ring
  have hpos : 0 < q * q' / (4 * q - q') := div_pos (mul_pos hq0 h0) hD
  unfold periodProfit revenue
  rw [e1, e2, demand_hi q _ q' _ _ h hq0 hs hs0 hs1 (by linarith)]
  have h1s : 1 - (2 * q - q') / (4 * q - q') = 2 * q / (4 * q - q') := by
    rw [eq_div_iff hDne, sub_mul, div_mul_cancel₀ _ hDne]; ring
  rw [h1s, div_mul_div_comm, sq (4 * q - q')]
  congr 1
  ring

lemma pp_lo (q q' : ℝ) (h0 : 0 < q) (h : q < q') :
    periodProfit q q' = q * q' * (q' - q) / (4 * q' - q) ^ 2 := by
  have hD : 0 < 4 * q' - q := by linarith
  have hDne : 4 * q' - q ≠ 0 := hD.ne'
  have e1 : eqPrice q q' = q * (q' - q) / (4 * q' - q) := by
    rw [eqPrice, if_neg (not_lt.2 h.le), if_pos h]
  have e2 : eqPrice q' q = 2 * q' * (q' - q) / (4 * q' - q) := by
    rw [eqPrice, if_pos h]
  have hs : 2 * q' * (q' - q) / (4 * q' - q) - q * (q' - q) / (4 * q' - q)
      = (q' - q) * ((2 * q' - q) / (4 * q' - q)) := by
    field_simp <;> ring
  have ht : q * (q' - q) / (4 * q' - q) = q * ((q' - q) / (4 * q' - q)) := by ring
  have ht0 : 0 ≤ (q' - q) / (4 * q' - q) := div_nonneg (by linarith) hD.le
  have hts : (q' - q) / (4 * q' - q) ≤ (2 * q' - q) / (4 * q' - q) := by
    rw [div_le_div_iff_of_pos_right hD]; linarith
  have hs1 : (2 * q' - q) / (4 * q' - q) ≤ 1 := (div_le_one hD).2 (by linarith)
  unfold periodProfit revenue
  rw [e1, e2, demand_lo q _ q' _ _ _ h h0 hs ht ht0 hts hs1]
  field_simp <;> ring

lemma pp_eq (q : ℝ) : periodProfit q q = 0 := by
  unfold periodProfit revenue
  simp [eqPrice]

lemma isNE_iff (P : Params) (a b : Bool) :
    IsNE P a b ↔ payoff P (!a) b ≤ payoff P a b ∧ payoff P (!b) a ≤ payoff P b a := by
  unfold IsNE AGT.IsPureNash testingGame profile
  constructor
  · intro h
    have h1 := h true (!a)
    have h2 := h false (!b)
    simp [Function.update] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩ i t
    cases i <;> cases t <;> cases a <;> cases b <;> simp_all [Function.update]

lemma quad_aux (a b c d e x : ℝ) (ha : 0 < a) (hd : d = b ^ 2 - 4 * a * c) (he : e = 2 * a)
    (hd0 : 0 ≤ d) :
    a * x ^ 2 - b * x + c = a * ((x - (b - √d) / e) * (x - (b + √d) / e)) := by
  subst he
  have hs : √d ^ 2 = d := Real.sq_sqrt hd0
  have h1 : (b - √d) / (2 * a) + (b + √d) / (2 * a) = b / a := by
    field_simp <;> ring
  have h2 : (b - √d) / (2 * a) * ((b + √d) / (2 * a)) = c / a := by
    rw [div_mul_div_comm, div_eq_div_iff (by positivity) ha.ne']
    linear_combination (-a) * hs + (-a) * hd
  have h3 : (x - (b - √d) / (2 * a)) * (x - (b + √d) / (2 * a))
      = x ^ 2 - x * ((b - √d) / (2 * a) + (b + √d) / (2 * a))
        + (b - √d) / (2 * a) * ((b + √d) / (2 * a)) := by ring
  rw [h3, h1, h2]
  field_simp <;> ring

lemma lohi (a b d e : ℝ) (ha : 0 < a) (he : e = 2 * a) : (b - √d) / e ≤ (b + √d) / e := by
  subst he
  have : (b + √d) / (2 * a) - (b - √d) / (2 * a) = √d / a := by field_simp <;> ring
  have : 0 ≤ √d / a := div_nonneg (Real.sqrt_nonneg d) ha.le
  linarith

lemma quad_le (a b c d e x : ℝ) (ha : 0 < a) (hd : d = b ^ 2 - 4 * a * c) (he : e = 2 * a) :
    a * x ^ 2 - b * x + c ≤ 0 ↔ 0 ≤ d ∧ (b - √d) / e ≤ x ∧ x ≤ (b + √d) / e := by
  have key : 4 * a * (a * x ^ 2 - b * x + c) = (2 * a * x - b) ^ 2 - d := by rw [hd]; ring
  have hlh := lohi a b d e ha he
  constructor
  · intro hQ
    have hd0 : 0 ≤ d := by nlinarith [sq_nonneg (2 * a * x - b)]
    rw [quad_aux a b c d e x ha hd he hd0] at hQ
    have hX : (x - (b - √d) / e) * (x - (b + √d) / e) ≤ 0 := by
      by_contra hc
      push Not at hc
      have := mul_pos ha hc
      linarith
    refine ⟨hd0, ?_, ?_⟩
    · by_contra hc
      push Not at hc
      nlinarith [mul_pos (sub_pos.2 hc) (sub_pos.2 (lt_of_lt_of_le hc hlh))]
    · by_contra hc
      push Not at hc
      nlinarith [mul_pos (sub_pos.2 hc) (sub_pos.2 (lt_of_le_of_lt hlh hc))]
  · rintro ⟨hd0, h1, h2⟩
    rw [quad_aux a b c d e x ha hd he hd0]
    have : 0 ≤ (x - (b - √d) / e) * ((b + √d) / e - x) :=
      mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)
    nlinarith

lemma quad_ge (a b c d e x : ℝ) (ha : 0 < a) (hd : d = b ^ 2 - 4 * a * c) (he : e = 2 * a) :
    0 ≤ a * x ^ 2 - b * x + c ↔ (0 ≤ d → x ≤ (b - √d) / e ∨ (b + √d) / e ≤ x) := by
  have key : 4 * a * (a * x ^ 2 - b * x + c) = (2 * a * x - b) ^ 2 - d := by rw [hd]; ring
  have hlh := lohi a b d e ha he
  constructor
  · intro hQ hd0
    rw [quad_aux a b c d e x ha hd he hd0] at hQ
    by_contra hc
    push Not at hc
    have := mul_pos (sub_pos.2 hc.1) (sub_pos.2 hc.2)
    nlinarith
  · intro h
    by_cases hd0 : 0 ≤ d
    · rw [quad_aux a b c d e x ha hd he hd0]
      rcases h hd0 with h1 | h1
      · have : 0 ≤ ((b - √d) / e - x) * ((b + √d) / e - x) :=
          mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 (h1.trans hlh))
        nlinarith
      · have : 0 ≤ (x - (b - √d) / e) * (x - (b + √d) / e) :=
          mul_nonneg (sub_nonneg.2 (hlh.trans h1)) (sub_nonneg.2 h1)
        nlinarith
    · push Not at hd0
      by_contra hc
      push Not at hc
      nlinarith [sq_nonneg (2 * a * x - b)]

lemma sign_aux (k X Y : ℝ) (hk : 0 < k) (h : k * X = -Y) :
    (0 ≤ X ↔ Y ≤ 0) ∧ (X ≤ 0 ↔ 0 ≤ Y) := by
  refine ⟨⟨fun h' => ?_, fun h' => ?_⟩, ⟨fun h' => ?_, fun h' => ?_⟩⟩
  · nlinarith
  · by_contra hc; push Not at hc; nlinarith
  · nlinarith
  · by_contra hc; push Not at hc; nlinarith

lemma st_aux (N0 D θ : ℝ) (hN : 0 < N0) (hθ : 0 < θ) :
    (N0 ≤ θ * D ↔ 0 < D ∧ N0 / D ≤ θ) ∧ (θ * D ≤ N0 ↔ (0 < D → θ ≤ N0 / D)) := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h hD => ?_, fun h => ?_⟩⟩
  · have hD : 0 < D := by
      by_contra hc; push Not at hc
      nlinarith [mul_nonneg hθ.le (neg_nonneg.2 hc)]
    exact ⟨hD, (div_le_iff₀ hD).2 h⟩
  · exact (div_le_iff₀ h.1).1 h.2
  · exact (le_div_iff₀ hD).2 h
  · by_cases hD : 0 < D
    · exact (le_div_iff₀ hD).1 (h hD)
    · push Not at hD
      nlinarith [mul_nonneg hθ.le (neg_nonneg.2 hD)]

end RecallTestingAux

open RecallTesting.Duopoly in
theorem solution (P : Params) (hS : P.Standing) :
    (IsNE P false false ↔ 0 ≤ discNT P ∧ thetaNTlo P ≤ P.θ ∧ P.θ ≤ thetaNThi P) ∧
    (IsNE P true true ↔ 0 < denST P ∧ thetaST P ≤ P.θ) ∧
    (IsNE P true false ↔
        (0 < denST P → P.θ ≤ thetaST P) ∧
        (0 ≤ discNT P → P.θ ≤ thetaNTlo P ∨ thetaNThi P ≤ P.θ)) ∧
    (IsNE P false true ↔ IsNE P true false) ∧
    ¬ (IsNE P false false ∧ IsNE P true true) := by
  obtain ⟨hV, hB, hρ, hδ, hδ1, hγ, hγ1, hθ, hθ1⟩ := hS
  have hW : 0 < P.V + P.B := by linarith
  have hL : 0 < (P.V + P.B) * (1 - P.γ) := mul_pos hW (by linarith)
  have hLH : (P.V + P.B) * (1 - P.γ) < P.V + P.B := by nlinarith
  have h3 : (3 + P.γ) ≠ 0 := by linarith
  have h34 : (3 * P.V + 4 * P.B) ≠ 0 := by linarith
  have hWne : P.V + P.B ≠ 0 := hW.ne'
  have e1 : periodProfit (P.V + P.B) P.V = 4 * (P.V + P.B) ^ 2 * P.B / (3 * P.V + 4 * P.B) ^ 2 := by
    rw [RecallTestingAux.pp_hi _ _ hV (by linarith), show P.V + P.B - P.V = P.B by ring,
      show 4 * (P.V + P.B) - P.V = 3 * P.V + 4 * P.B by ring]
  have e2 : periodProfit P.V (P.V + P.B) = P.V * (P.V + P.B) * P.B / (3 * P.V + 4 * P.B) ^ 2 := by
    rw [RecallTestingAux.pp_lo _ _ hV (by linarith), show P.V + P.B - P.V = P.B by ring,
      show 4 * (P.V + P.B) - P.V = 3 * P.V + 4 * P.B by ring]
  have e3 : periodProfit (P.V + P.B) ((P.V + P.B) * (1 - P.γ))
      = 4 * (P.V + P.B) * P.γ / (3 + P.γ) ^ 2 := by
    rw [RecallTestingAux.pp_hi _ _ hL hLH, show P.V + P.B - (P.V + P.B) * (1 - P.γ) = (P.V + P.B) * P.γ by ring,
      show 4 * (P.V + P.B) - (P.V + P.B) * (1 - P.γ) = (P.V + P.B) * (3 + P.γ) by ring]
    field_simp <;> ring
  have e4 : periodProfit ((P.V + P.B) * (1 - P.γ)) (P.V + P.B)
      = (P.V + P.B) * (1 - P.γ) * P.γ / (3 + P.γ) ^ 2 := by
    rw [RecallTestingAux.pp_lo _ _ hL hLH, show P.V + P.B - (P.V + P.B) * (1 - P.γ) = (P.V + P.B) * P.γ by ring,
      show 4 * (P.V + P.B) - (P.V + P.B) * (1 - P.γ) = (P.V + P.B) * (3 + P.γ) by ring]
    field_simp <;> ring
  have hTT : payoff P true true = 0 := by
    simp [payoff, qual1, qual2, failProb, RecallTestingAux.pp_eq]
  have hTN : payoff P true false = periodProfit P.V (P.V + P.B)
      + P.θ * periodProfit (P.V + P.B) ((P.V + P.B) * (1 - P.γ)) := by
    simp [payoff, qual1, qual2, failProb, RecallTestingAux.pp_eq]
  have hNT : payoff P false true = periodProfit (P.V + P.B) P.V
      - P.θ * (P.ρ + P.δ * periodProfit (P.V + P.B) P.V)
      + P.θ * periodProfit ((P.V + P.B) * (1 - P.γ)) (P.V + P.B) := by
    simp [payoff, qual1, qual2, failProb, RecallTestingAux.pp_eq]
  have hNN : payoff P false false = - (P.θ * P.ρ)
      + P.θ * (1 - P.θ) * periodProfit ((P.V + P.B) * (1 - P.γ)) (P.V + P.B)
      + (1 - P.θ) * P.θ * periodProfit (P.V + P.B) ((P.V + P.B) * (1 - P.γ)) := by
    simp [payoff, qual1, qual2, failProb, RecallTestingAux.pp_eq]
    ring
  simp only [e1, e2, e3, e4] at hNT hNN hTN
  -- quadratic for the no-test equilibrium
  have hQ : (3 + P.γ) ^ 2 * (payoff P false false - payoff P true false)
      = -(((P.V + P.B) * (5 - P.γ) * P.γ) * P.θ ^ 2 - bNT P * P.θ
          + P.V * (P.V + P.B) * P.B * (3 + P.γ) ^ 2 / (3 * P.V + 4 * P.B) ^ 2) := by
    rw [hNN, hTN]; unfold bNT; field_simp <;> ring
  have ha : 0 < (P.V + P.B) * (5 - P.γ) * P.γ := by
    have : 0 < 5 - P.γ := by linarith
    positivity
  have hdisc : discNT P = bNT P ^ 2 - 4 * ((P.V + P.B) * (5 - P.γ) * P.γ)
      * (P.V * (P.V + P.B) * P.B * (3 + P.γ) ^ 2 / (3 * P.V + 4 * P.B) ^ 2) := by
    unfold discNT; ring
  have he : 2 * (P.V + P.B) * (5 - P.γ) * P.γ = 2 * ((P.V + P.B) * (5 - P.γ) * P.γ) := by ring
  have hql := RecallTestingAux.quad_le _ _ _ _ _ P.θ ha hdisc he
  have hqg := RecallTestingAux.quad_ge _ _ _ _ _ P.θ ha hdisc he
  have hsq := RecallTestingAux.sign_aux _ _ _ (by positivity) hQ
  -- the dual-test cutoff
  have hK : 0 < (3 * P.V + 4 * P.B) ^ 2 * (3 + P.γ) ^ 2 := by positivity
  have hST : (3 * P.V + 4 * P.B) ^ 2 * (3 + P.γ) ^ 2 * payoff P false true
      = -(P.θ * denST P - 4 * P.B * (P.V + P.B) ^ 2 * (3 + P.γ) ^ 2) := by
    rw [hNT]; unfold denST; field_simp <;> ring
  have hsst := RecallTestingAux.sign_aux _ _ _ hK hST
  have hst := RecallTestingAux.st_aux (4 * P.B * (P.V + P.B) ^ 2 * (3 + P.γ) ^ 2) (denST P) P.θ
    (by positivity) hθ
  have hlo : thetaNTlo P = (bNT P - √(discNT P)) / (2 * (P.V + P.B) * (5 - P.γ) * P.γ) := rfl
  have hhi : thetaNThi P = (bNT P + √(discNT P)) / (2 * (P.V + P.B) * (5 - P.γ) * P.γ) := rfl
  have hthST : thetaST P = 4 * P.B * (P.V + P.B) ^ 2 * (3 + P.γ) ^ 2 / denST P := rfl
  have iNN : IsNE P false false ↔ payoff P true false ≤ payoff P false false := by
    rw [RecallTestingAux.isNE_iff]; simp
  have iTT : IsNE P true true ↔ payoff P false true ≤ 0 := by
    rw [RecallTestingAux.isNE_iff]; simp [hTT]
  have iTN : IsNE P true false ↔
      payoff P false false ≤ payoff P true false ∧ 0 ≤ payoff P false true := by
    rw [RecallTestingAux.isNE_iff]; simp [hTT]
  have iFT : IsNE P false true ↔
      0 ≤ payoff P false true ∧ payoff P false false ≤ payoff P true false := by
    rw [RecallTestingAux.isNE_iff]; simp [hTT]
  have c1 : IsNE P false false ↔ 0 ≤ discNT P ∧ thetaNTlo P ≤ P.θ ∧ P.θ ≤ thetaNThi P := by
    rw [iNN, ← sub_nonneg, hsq.1, hql, hlo, hhi]
  have c2 : IsNE P true true ↔ 0 < denST P ∧ thetaST P ≤ P.θ := by
    rw [iTT, hsst.2, sub_nonneg, hst.1, hthST]
  have c3 : IsNE P true false ↔
      (0 < denST P → P.θ ≤ thetaST P) ∧
        (0 ≤ discNT P → P.θ ≤ thetaNTlo P ∨ thetaNThi P ≤ P.θ) := by
    rw [iTN, ← sub_nonpos, hsq.2, hqg, hsst.1, sub_nonpos, hst.2, hthST, hlo, hhi, and_comm]
  refine ⟨c1, c2, c3, by rw [iFT, iTN, and_comm], ?_⟩
  rintro ⟨hn, ht⟩
  rw [iNN] at hn
  rw [iTT] at ht
  have hθδ : P.θ * P.δ ≤ 1 := by nlinarith
  have hA1 : 0 ≤ 4 * (P.V + P.B) ^ 2 * P.B / (3 * P.V + 4 * P.B) ^ 2 * (1 - P.θ * P.δ) :=
    mul_nonneg (by positivity) (by linarith)
  have hA2 : 0 < P.V * (P.V + P.B) * P.B / (3 * P.V + 4 * P.B) ^ 2 := by positivity
  have hH1 : 0 ≤ 4 * (P.V + P.B) * P.γ / (3 + P.γ) ^ 2 := by positivity
  have hH2 : 0 ≤ (P.V + P.B) * (1 - P.γ) * P.γ / (3 + P.γ) ^ 2 :=
    div_nonneg (mul_nonneg hL.le hγ.le) (by positivity)
  have hid : payoff P false true - (payoff P false false - payoff P true false)
      = 4 * (P.V + P.B) ^ 2 * P.B / (3 * P.V + 4 * P.B) ^ 2 * (1 - P.θ * P.δ)
        + P.V * (P.V + P.B) * P.B / (3 * P.V + 4 * P.B) ^ 2
        + P.θ ^ 2 * (4 * (P.V + P.B) * P.γ / (3 + P.γ) ^ 2
          + (P.V + P.B) * (1 - P.γ) * P.γ / (3 + P.γ) ^ 2) := by
    rw [hNT, hNN, hTN]; ring
  have : 0 ≤ P.θ ^ 2 * (4 * (P.V + P.B) * P.γ / (3 + P.γ) ^ 2
          + (P.V + P.B) * (1 - P.γ) * P.γ / (3 + P.γ) ^ 2) :=
    mul_nonneg (sq_nonneg _) (add_nonneg hH1 hH2)
  linarith
