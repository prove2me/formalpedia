-- Prove2me | solution 1 for TechSourcing.PTS.lemma_1_loan
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T03:50:25.73455+00:00
-- url     : https://prove2.me/submissions/7764b7f1-3153-4236-927a-a3bc5bc5fa84

import Mathlib
import Definitions.Def_TechSourcing_PTS_Model
import Theorems.Thm_TechSourcing_PTS_lemma_A1_phiHat
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

namespace LoanCoreTS

lemma vertex (P : Params) (hP : P.Standing) (π : ℝ) (hπ : 0 < π) :
    ∃ t : ℝ, 0 < t ∧ π = 6 * t ^ 2 / P.a + 2 * (1 / P.a + 3 / P.b) * t := by
  have ha := hP.1
  have hb := hP.2.1
  set A := 1 / P.a + 3 / P.b with hA
  have hApos : 0 < A := by positivity
  set r := Real.sqrt (A ^ 2 + 6 * π / P.a) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hden : 0 < r + A := by linarith
  have hr2 : r ^ 2 = A ^ 2 + 6 * π / P.a := Real.sq_sqrt (by positivity)
  refine ⟨π / (r + A), by positivity, ?_⟩
  set t := π / (r + A)
  have htr : t * (r + A) = π := by simp only [t]; field_simp
  have h6 : 6 * t / P.a = r - A := by
    have : (r - A) * (r + A) = 6 * π / P.a := by nlinarith
    have h' : 6 * t / P.a * (r + A) = 6 * π / P.a := by rw [← htr]; ring
    exact mul_right_cancel₀ hden.ne' (h'.trans this.symm)
  have : 6 * t ^ 2 / P.a + 2 * A * t = t * (6 * t / P.a) + 2 * A * t := by ring
  rw [this, h6]; linarith

lemma piPhi_phiHat (P : Params) (hP : P.Standing) (θ : ℝ) :
    piPhi P (phiHat P θ) = Wb P - Lb P + Lb P * θ := by
  have hc := hP.2.2.1
  unfold piPhi phiHat Wb Lb; field_simp; ring

lemma fixedL (P : Params) (hP : P.Standing) (hWL : Lb P < Wb P) (o : LoanOutcome) (φ : ℝ)
    (h : IsLoanEq P o φ) (hθ1 : o.θ < 1) :
    6 * o.θ ^ 2 / P.a + 2 * (1 / P.a + 3 / P.b) * o.θ = Wb P - Lb P + Lb P * o.θ ∧
      φ = phiHat P o.θ := by
  have ha := hP.1
  have hb := hP.2.1
  obtain ⟨hbr, hex⟩ := (isLoanEq_iff P o φ).1 h
  have hφ := (lemma_A1_phiHat P hP o.θ hθ1.le φ).1 hex
  refine ⟨?_, hφ⟩
  have hθ0 : 0 ≤ o.θ := hbr.1.2.2.1.1
  have hLnn : 0 ≤ Lb P := by
    unfold Lb; have : 0 ≤ 1 - P.β := by linarith [hP.2.2.2.2.2.2]
    have := hP.2.2.1; have := hP.2.2.2.1; have := hP.2.2.2.2.2.1
    positivity
  have hπ : piPhi P φ = Wb P - Lb P + Lb P * o.θ := by rw [hφ]; exact piPhi_phiHat P hP _
  have hπpos : 0 < piPhi P φ := by rw [hπ]; nlinarith
  set A := 1 / P.a + 3 / P.b with hA
  have hApos : 0 < A := by positivity
  by_cases hbig : 6 / P.a + 2 * A ≤ piPhi P φ
  · exfalso
    have h1 := br_le P hP φ o hbr 1 one_pos le_rfl
    unfold LoanCoreTS.hL at h1
    rw [← hA] at h1
    have hfac : (1 * piPhi P φ - 2 * 1 ^ 3 / P.a - A * 1 ^ 2)
        - (o.θ * piPhi P φ - 2 * o.θ ^ 3 / P.a - A * o.θ ^ 2)
        = (1 - o.θ) * (piPhi P φ - 2 * (1 + o.θ + o.θ ^ 2) / P.a - A * (1 + o.θ)) := by ring
    have hpos : 0 < piPhi P φ - 2 * (1 + o.θ + o.θ ^ 2) / P.a - A * (1 + o.θ) := by
      have : 2 * (1 + o.θ + o.θ ^ 2) / P.a < 6 / P.a := by
        apply div_lt_div_of_pos_right _ ha; nlinarith
      nlinarith
    have := mul_pos (show 0 < 1 - o.θ by linarith) hpos
    linarith
  · push Not at hbig
    obtain ⟨t, ht0, htπ⟩ := vertex P hP _ hπpos
    rw [← hA] at htπ
    have ht1 : t < 1 := by
      by_contra hc'; push Not at hc'
      have : 6 / P.a ≤ 6 * t ^ 2 / P.a := by
        apply div_le_div_of_nonneg_right _ ha.le; nlinarith
      nlinarith
    have := br_le P hP φ o hbr t ht0 ht1.le
    have hθt := uniq P hP _ t o.θ ht0.le hθ0 htπ this
    rw [hθt] at hπ
    rw [hθt, ← htπ, hπ]

end LoanCoreTS

open LoanCoreTS in
theorem solution (P : Params) (hP : P.Standing) (hWL : Lb P < Wb P) :
    (∀ (o : LoanOutcome) (φ : ℝ), IsLoanEq P o φ → o.θ < 1 →
        o.θ = thetaLStar P ∧ φ = phiHat P (thetaLStar P)) ∧
      (0 < thetaLStar P → thetaLStar P < 1 → ∃ (o : LoanOutcome) (φ : ℝ), IsLoanEq P o φ) := by
  have ha := hP.1
  have hb := hP.2.1
  have hK : 0 < Wb P - Lb P := by linarith
  set X := 1 + 3 * P.a / P.b - P.a / 2 * Lb P with hX
  have hXa : X = P.a * (1 / P.a + 3 / P.b - Lb P / 2) := by
    simp only [hX]; field_simp
  refine ⟨fun o φ h hθ1 => ?_, fun h0 h1 => ?_⟩
  · obtain ⟨hfix, hφ⟩ := fixedL P hP hWL o φ h hθ1
    have hθ0 : 0 ≤ o.θ := (((isLoanEq_iff P o φ).1 h).1.1).2.2.1.1
    have key : 36 * o.θ ^ 2 + 12 * o.θ * X = 6 * P.a * (Wb P - Lb P) := by
      have ha' := ha.ne'
      have hb' := hb.ne'
      have h2 := hfix
      field_simp at h2
      simp only [hX]
      field_simp
      linarith [h2]
    have hsq : (6 * o.θ + X) ^ 2 = X ^ 2 + 6 * P.a * (Wb P - Lb P) := by
      linear_combination key
    have hnn : 0 ≤ 6 * o.θ + X := by
      by_contra hc; push Not at hc
      have : X ^ 2 < (6 * o.θ + X) ^ 2 := by rw [hsq]; nlinarith [mul_pos ha hK]
      nlinarith
    have hθ : o.θ = thetaLStar P := by
      unfold thetaLStar
      rw [← hX, ← hsq, Real.sqrt_sq hnn]; ring
    exact ⟨hθ, hθ ▸ hφ⟩
  · set t := thetaLStar P with htdef
    have hroot : Real.sqrt (X ^ 2 + 6 * P.a * (Wb P - Lb P)) = 6 * t + X := by
      simp only [htdef, thetaLStar]; rw [← hX]; ring
    have hsq : (6 * t + X) ^ 2 = X ^ 2 + 6 * P.a * (Wb P - Lb P) := by
      rw [← hroot]; exact Real.sq_sqrt (by nlinarith [mul_pos ha hK])
    set φ := phiHat P t
    have hπ : piPhi P φ = 6 * t ^ 2 / P.a + 2 * (1 / P.a + 3 / P.b) * t := by
      rw [piPhi_phiHat P hP t]
      have key : 36 * t ^ 2 + 12 * t * X = 6 * P.a * (Wb P - Lb P) := by
        linear_combination hsq
      have ha' := ha.ne'
      have hb' := hb.ne'
      simp only [hX] at key
      field_simp at key
      field_simp
      linarith [key]
    obtain ⟨o, ho, hθ, hU⟩ := construct P hP t h0 h1.le
    have hbr : IsManufBR_L P φ o := br_of_max P hP φ o ho (by rw [hU φ, hθ]) fun x hx _ => by
      rw [hθ]
      have := h_gap P _ t x hπ
      have : 0 ≤ (t - x) ^ 2 * (2 * (2 * t + x) / P.a + (1 / P.a + 3 / P.b)) := by positivity
      linarith
    refine ⟨o, φ, (isLoanEq_iff P o φ).2 ⟨hbr, ?_⟩⟩
    rw [hθ]
    exact (lemma_A1_phiHat P hP t h1.le φ).2 rfl
