-- Prove2me | solution 1 for TechSourcing.PTS.lemma_A1_loan
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T03:48:06.48701+00:00
-- url     : https://prove2.me/submissions/25eb0210-10f0-4fcb-9054-342bbf00b4a5

import Mathlib
import Definitions.Def_TechSourcing_PTS_Model
open TechSourcing.PTS

namespace LoanCoreTS

/-- `h(x) = xπ − 2x³/a − (1/a + 3/b)x²`. -/
noncomputable def hL (P : Params) (π x : ℝ) : ℝ :=
  x * π - 2 * x ^ 3 / P.a - (1 / P.a + 3 / P.b) * x ^ 2

lemma UNL_eq (P : Params) (B pay θ S : ℝ) (hS : 0 ≤ S) (hK : 0 ≤ K P θ) :
    UNL P B pay θ S = -θ * K P θ + (1 - θ) * S - G P θ + θ * pay := by
  unfold UNL
  rw [min_eq_left (by linarith)]
  ring

lemma UL_eq (P : Params) (φ B pay θ S : ℝ) (hS : 0 ≤ S) (hK : 0 ≤ K P θ) :
    UL P φ B pay θ S = θ * (piPhi P φ - pay) - (1 - θ) * (K P θ + S)
      + P.β * (P.R - φ) * P.D := by
  unfold UL piPhi
  rw [min_eq_left (by linarith)]
  ring

lemma feas_nonneg (P : Params) (hP : P.Standing) {B BG θ S : ℝ} (h : Feasible P B BG θ S) :
    0 ≤ S ∧ 0 ≤ K P θ ∧ 0 ≤ θ := by
  obtain ⟨ha, hb, -⟩ := hP
  obtain ⟨h0, -, hG, -⟩ := h
  have : 0 ≤ G P θ := by unfold G; positivity
  exact ⟨by linarith, by unfold K; positivity, h0⟩

set_option maxHeartbeats 2000000 in
/-- pay bound from IC. -/
lemma pay_bound (P : Params) (hP : P.Standing) (o : LoanOutcome) (ho : o.Admissible P) :
    o.θ * (o.S + 3 * o.θ ^ 2 / P.a + 2 * o.θ / P.b) ≤ o.θ * o.pay := by
  have hP' := hP
  obtain ⟨ha, hb, hc, hD, hR, hβ0, hβ1⟩ := hP
  obtain ⟨hB, hBG, hF, hIC, hIR⟩ := ho
  obtain ⟨hS0, hK0, -⟩ := feas_nonneg P hP' hF
  obtain ⟨hθ0, hθ1, hGS, hSBG, hSKB, hmin⟩ := hF
  rcases hθ0.lt_or_eq with hθ | hθ
  swap
  · rw [← hθ]; simp
  apply mul_le_mul_of_nonneg_left _ hθ.le
  set k := 3 * o.θ / P.a + 1 / P.b with hk
  have hkpos : 0 < k := by positivity
  set D0 := o.pay - o.S - 3 * o.θ ^ 2 / P.a - 2 * o.θ / P.b with hD0
  have hdev : ∀ ε : ℝ, 0 < ε → ε ≤ o.θ → 0 ≤ D0 + ε * k := by
    intro ε hε hεθ
    have hsq : (o.θ - ε) ^ 2 ≤ o.θ ^ 2 := by nlinarith
    have hfe : Feasible P o.B o.BG (o.θ - ε) o.S := by
      refine ⟨by linarith, by linarith, ?_, hSBG, ?_, le_trans (by linarith) hmin⟩
      · unfold G at hGS ⊢
        have := div_le_div_of_nonneg_right hsq hb.le
        linarith
      · unfold K at hSKB ⊢
        have := div_le_div_of_nonneg_right hsq ha.le
        linarith
    have hK' : 0 ≤ K P (o.θ - ε) := by unfold K; positivity
    have hic := hIC _ _ hfe
    rw [UNL_eq P _ _ _ _ hS0 hK', UNL_eq P _ _ _ _ hS0 hK0] at hic
    have hdiff : (-o.θ * K P o.θ + (1 - o.θ) * o.S - G P o.θ + o.θ * o.pay)
        - (-(o.θ - ε) * K P (o.θ - ε) + (1 - (o.θ - ε)) * o.S - G P (o.θ - ε)
            + (o.θ - ε) * o.pay)
        = ε * (D0 + ε * (3 * o.θ - ε) / P.a + ε / P.b) := by
      simp only [K, G, hD0]; field_simp; ring
    have h1 : 0 ≤ ε * (D0 + ε * (3 * o.θ - ε) / P.a + ε / P.b) := by linarith
    have h2 : 0 ≤ D0 + ε * (3 * o.θ - ε) / P.a + ε / P.b := by
      by_contra hc'; push Not at hc'
      have := mul_neg_of_pos_of_neg hε hc'
      linarith
    have h3 : ε * (3 * o.θ - ε) / P.a ≤ ε * (3 * o.θ / P.a) := by
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ hε.le
      exact div_le_div_of_nonneg_right (by linarith) ha.le
    have : ε * k = ε * (3 * o.θ / P.a) + ε / P.b := by simp only [hk]; ring
    linarith
  have h2 : 0 ≤ D0 := by
    by_contra hc'; push Not at hc'
    set ε := min o.θ (-D0 / (2 * k))
    have hε : 0 < ε := lt_min hθ (by apply div_pos (by linarith) (by positivity))
    have h := hdev ε hε (min_le_left _ _)
    have : ε * k ≤ -D0 / 2 := by
      have := min_le_right o.θ (-D0 / (2 * k))
      calc ε * k ≤ -D0 / (2 * k) * k := mul_le_mul_of_nonneg_right this hkpos.le
        _ = -D0 / 2 := by field_simp
    linarith
  simp only [hD0] at h2
  linarith

lemma upper (P : Params) (hP : P.Standing) (φ : ℝ) (o : LoanOutcome) (ho : o.Admissible P) :
    UL P φ o.B o.pay o.θ o.S ≤ hL P (piPhi P φ) o.θ + P.β * (P.R - φ) * P.D := by
  have hb := hP.2.1
  have ha := hP.1
  obtain ⟨hS0, hK0, hθ0⟩ := feas_nonneg P hP ho.2.2.1
  have hGS := ho.2.2.1.2.2.1
  have hθ1 := ho.2.2.1.2.1
  rw [UL_eq P φ _ _ _ _ hS0 hK0]
  have hpb := pay_bound P hP o ho
  unfold hL
  unfold K
  unfold G at hGS
  have key : (o.θ * piPhi P φ - 2 * o.θ ^ 3 / P.a - (1 / P.a + 3 / P.b) * o.θ ^ 2)
      - (o.θ * (piPhi P φ - o.pay) - (1 - o.θ) * (o.θ ^ 2 / P.a + o.S))
      = (o.θ * o.pay - o.θ * (o.S + 3 * o.θ ^ 2 / P.a + 2 * o.θ / P.b)) + (o.S - o.θ ^ 2 / P.b) := by
    ring
  linarith

lemma construct (P : Params) (hP : P.Standing) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∃ o : LoanOutcome, o.Admissible P ∧ o.θ = t ∧
      ∀ φ, UL P φ o.B o.pay o.θ o.S = hL P (piPhi P φ) t + P.β * (P.R - φ) * P.D := by
  have hP' := hP
  obtain ⟨ha, hb, hc, hD, hR, hβ0, hβ1⟩ := hP
  set pay := t ^ 2 / P.b + 3 * t ^ 2 / P.a + 2 * t / P.b with hpay
  refine ⟨⟨t ^ 2 / P.a + t ^ 2 / P.b, t ^ 2 / P.b, pay, t, t ^ 2 / P.b⟩, ?_, rfl, ?_⟩
  · have hBG : Ginv P (t ^ 2 / P.b) = t := by
      unfold Ginv; rw [show P.b * (t ^ 2 / P.b) = t ^ 2 by field_simp]
      exact Real.sqrt_sq ht0.le
    have hB2 : Ginv P (P.a * (t ^ 2 / P.a + t ^ 2 / P.b) / (P.a + P.b)) = t := by
      rw [show P.a * (t ^ 2 / P.a + t ^ 2 / P.b) / (P.a + P.b) = t ^ 2 / P.b by
        field_simp; ring]
      exact hBG
    have hS0 : (0:ℝ) ≤ t ^ 2 / P.b := by positivity
    have hKt : 0 ≤ K P t := by unfold K; positivity
    refine ⟨by positivity, by positivity, ?_, ?_, ?_⟩
    · refine ⟨ht0.le, ht1, le_refl _, le_refl _, ?_, ?_⟩
      · unfold K; linarith
      · simp only; rw [hBG, hB2, min_self]
    · intro θ' S' hF'
      obtain ⟨hS0', hK0', hθ0'⟩ := feas_nonneg P hP' hF'
      obtain ⟨-, h1', hG', hS', -, -⟩ := hF'
      unfold G at hG'
      have hθt : θ' ≤ t := by
        have : θ' ^ 2 ≤ t ^ 2 := by
          have := le_trans hG' hS'
          exact (div_le_div_iff_of_pos_right hb).1 this
        nlinarith
      simp only
      rw [UNL_eq P _ _ _ _ hS0' hK0', UNL_eq P _ _ _ _ hS0 hKt]
      simp only [K, G]
      have hx : 0 ≤ t - θ' := by linarith
      have h1 : (1 - θ') * S' ≤ (1 - θ') * (t ^ 2 / P.b) :=
        mul_le_mul_of_nonneg_left hS' (by linarith)
      have key : -t * (t ^ 2 / P.a) + (1 - t) * (t ^ 2 / P.b) - t ^ 2 / P.b + t * pay
          - (-θ' * (θ' ^ 2 / P.a) + (1 - θ') * (t ^ 2 / P.b) - θ' ^ 2 / P.b + θ' * pay)
          = (t - θ') ^ 2 * ((2 * t + θ') / P.a + 1 / P.b) := by
        simp only [hpay]; field_simp; ring
      have : 0 ≤ (t - θ') ^ 2 * ((2 * t + θ') / P.a + 1 / P.b) := by positivity
      linarith
    · simp only
      rw [UNL_eq P _ _ _ _ hS0 hKt]
      simp only [K, G, hpay]
      have : -t * (t ^ 2 / P.a) + (1 - t) * (t ^ 2 / P.b) - t ^ 2 / P.b
          + t * (t ^ 2 / P.b + 3 * t ^ 2 / P.a + 2 * t / P.b)
          = 2 * t ^ 3 / P.a + 2 * t ^ 2 / P.b := by ring
      rw [this]
      positivity
  · intro φ
    simp only
    have hS0 : (0:ℝ) ≤ t ^ 2 / P.b := by positivity
    have hKt : 0 ≤ K P t := by unfold K; positivity
    rw [UL_eq P φ _ _ _ _ hS0 hKt]
    simp only [hL, K, hpay]
    field_simp; ring

/-- `h(t) − h(x) = (t − x)² (2(2t + x)/a + A)` when `π = 6t²/a + 2At`. -/
lemma h_gap (P : Params) (π t x : ℝ) (hπ : π = 6 * t ^ 2 / P.a + 2 * (1 / P.a + 3 / P.b) * t) :
    hL P π t - hL P π x = (t - x) ^ 2 * (2 * (2 * t + x) / P.a + (1 / P.a + 3 / P.b)) := by
  unfold hL; rw [hπ]; ring

lemma br_le (P : Params) (hP : P.Standing) (φ : ℝ) (o : LoanOutcome) (ho : IsManufBR_L P φ o)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    hL P (piPhi P φ) t ≤ hL P (piPhi P φ) o.θ := by
  obtain ⟨o', ho', hθ', hU⟩ := construct P hP t ht0 ht1
  have h1 := ho.2 o' ho'
  have h2 := upper P hP φ o ho.1
  rw [hU φ] at h1
  linarith

lemma br_of_max (P : Params) (hP : P.Standing) (φ : ℝ) (o : LoanOutcome) (ho : o.Admissible P)
    (hU : UL P φ o.B o.pay o.θ o.S = hL P (piPhi P φ) o.θ + P.β * (P.R - φ) * P.D)
    (hmax : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → hL P (piPhi P φ) x ≤ hL P (piPhi P φ) o.θ) :
    IsManufBR_L P φ o := by
  refine ⟨ho, fun o' ho' => ?_⟩
  have h1 := upper P hP φ o' ho'
  have hf := ho'.2.2.1
  have h2 := hmax o'.θ hf.1 hf.2.1
  rw [hU]
  linarith

/-- the vertex is unique among `x ≥ 0`. -/
lemma uniq (P : Params) (hP : P.Standing) (π t x : ℝ) (ht : 0 ≤ t) (hx : 0 ≤ x)
    (hπ : π = 6 * t ^ 2 / P.a + 2 * (1 / P.a + 3 / P.b) * t) (h : hL P π t ≤ hL P π x) :
    x = t := by
  have ha := hP.1
  have hb := hP.2.1
  have hg := h_gap P π t x hπ
  have hc : 0 < 2 * (2 * t + x) / P.a + (1 / P.a + 3 / P.b) := by positivity
  have : (t - x) ^ 2 * (2 * (2 * t + x) / P.a + (1 / P.a + 3 / P.b)) ≤ 0 := by linarith
  have : (t - x) ^ 2 ≤ 0 := by
    by_contra h'; push Not at h'
    have := mul_pos h' hc
    linarith
  nlinarith [sq_nonneg (t - x)]

end LoanCoreTS

open LoanCoreTS in
theorem solution (P : Params) (hP : P.Standing) (φ : ℝ) (hφ : φ ≤ 1)
    (h0 : 0 < thetaHatL P φ) (h1 : thetaHatL P φ < 1) :
    (∃ o : LoanOutcome, IsManufBR_L P φ o) ∧
      ∀ o : LoanOutcome, IsManufBR_L P φ o → o.θ = thetaHatL P φ := by
  have ha := hP.1
  have hb := hP.2.1
  set t := thetaHatL P φ with htdef
  set A := 1 / P.a + 3 / P.b with hA
  have hApos : 0 < A := by positivity
  set r := Real.sqrt (A ^ 2 + 6 * piPhi P φ / P.a) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hden : 0 < r + A := by linarith
  have htr : t * (r + A) = piPhi P φ := by
    simp only [htdef, thetaHatL]; rw [← hA, ← hr]; field_simp
  have hπpos : 0 < piPhi P φ := by rw [← htr]; positivity
  have hr2 : r ^ 2 = A ^ 2 + 6 * piPhi P φ / P.a := Real.sq_sqrt (by positivity)
  have hπ : piPhi P φ = 6 * t ^ 2 / P.a + 2 * (1 / P.a + 3 / P.b) * t := by
    rw [← hA]
    -- 6t/a = r - A
    have h6 : 6 * t / P.a = r - A := by
      have : (r - A) * (r + A) = 6 * piPhi P φ / P.a := by nlinarith
      have h' : 6 * t / P.a * (r + A) = 6 * piPhi P φ / P.a := by
        rw [← htr]; ring
      have := mul_right_cancel₀ hden.ne' (h'.trans this.symm)
      exact this
    have : 6 * t ^ 2 / P.a + 2 * A * t = t * (6 * t / P.a) + 2 * A * t := by ring
    rw [this, h6]; linarith
  refine ⟨?_, fun o ho => uniq P hP _ t o.θ h0.le ho.1.2.2.1.1 hπ (br_le P hP φ o ho t h0 h1.le)⟩
  obtain ⟨o, ho, hθ, hU⟩ := construct P hP t h0 h1.le
  refine ⟨o, br_of_max P hP φ o ho (by rw [hU φ, hθ]) fun x hx _ => ?_⟩
  rw [hθ]
  have := h_gap P _ t x hπ
  have : 0 ≤ (t - x) ^ 2 * (2 * (2 * t + x) / P.a + (1 / P.a + 3 / P.b)) := by positivity
  linarith
