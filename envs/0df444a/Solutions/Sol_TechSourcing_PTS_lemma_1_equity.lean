-- Prove2me | solution 1 for TechSourcing.PTS.lemma_1_equity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T03:45:14.849401+00:00
-- url     : https://prove2.me/submissions/4e63386b-6eed-46d6-af68-3e69097b4052

import Mathlib
import Definitions.Def_TechSourcing_PTS_Model
import Theorems.Thm_TechSourcing_PTS_lemma_A1_phiHat
open TechSourcing.PTS

namespace EqCoreTS

/-- algebraic facts about `d = denE/2` and `γ̂`. -/
lemma alg (P : Params) (ha : 0 < P.a) (hb : 0 < P.b) :
    gammaHat P * (denE P / 2) = 1 / P.a + 1 / P.b ∧
    (1 - gammaHat P) * (denE P / 2 - 2 / P.a) = 2 / P.b ∧
    0 < denE P / 2 - 2 / P.a ∧ 0 < gammaHat P ∧ gammaHat P < 1 := by
  have hs2 : TechSourcing.PTS.sq P ^ 2 = 9 * P.a ^ 2 + 10 * P.a * P.b + P.b ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ TechSourcing.PTS.sq P := Real.sqrt_nonneg _
  have hsl : 3 * P.a + P.b < TechSourcing.PTS.sq P := by nlinarith
  have hsu : TechSourcing.PTS.sq P < 3 * P.a + 5 * P.b / 3 := by nlinarith
  have hsm : 3 * P.a - P.b < TechSourcing.PTS.sq P := by linarith
  have ha' := ha.ne'
  have hb' := hb.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold gammaHat denE; field_simp; linear_combination (-(1:ℝ)) * hs2
  · unfold gammaHat denE; field_simp; linear_combination (1:ℝ) * hs2
  · unfold denE
    have : 0 < TechSourcing.PTS.sq P / (P.a * P.b) - 1 / P.a := by
      rw [div_sub_div _ _ (by positivity) ha', div_pos_iff]; left
      constructor
      · nlinarith
      · positivity
    have h3 : 0 < 3 / P.b := by positivity
    rw [show (3 / P.a + 3 / P.b + TechSourcing.PTS.sq P / (P.a * P.b)) / 2 - 2 / P.a
      = (3 / P.b + (TechSourcing.PTS.sq P / (P.a * P.b) - 1 / P.a)) / 2 by ring]
    positivity
  · unfold gammaHat; apply div_pos _ (by positivity); linarith
  · unfold gammaHat; rw [div_lt_one (by positivity)]; linarith

/-- the manufacturer's equity payoff under fair valuation. -/
lemma UE_eq (P : Params) (φ : ℝ) (o : EqOutcome) (ho : o.Admissible P) :
    UE P φ o.γ o.B o.pay o.θ o.S = o.θ * (piPhi P φ - o.pay) + P.β * (P.R - φ) * P.D := by
  obtain ⟨-, -, -, -, -, -, hfair, -⟩ := ho
  unfold UE; rw [hfair]; unfold piPhi; ring

set_option maxHeartbeats 2000000 in
/-- pay bound: `θ² d ≤ θ pay` at every admissible equity outcome. -/
lemma pay_bound (P : Params) (hP : P.Standing) (o : EqOutcome) (ho : o.Admissible P) :
    o.θ ^ 2 * (denE P / 2) ≤ o.θ * o.pay ∧
      (0 < o.θ → o.γ * o.pay ≥ o.θ * (1 / P.a + 1 / P.b) ∧
        (1 - o.γ) * (o.pay - 2 * o.θ / P.a) ≥ 2 * o.θ / P.b) := by
  obtain ⟨ha, hb, hc, hD, hR, hβ0, hβ1⟩ := hP
  obtain ⟨hB, hBG, hγ0, hγ1, hF, hIC, hfair, hIR⟩ := ho
  obtain ⟨hθ0, hθ1, hGS, hSBG, hSKB, hmin⟩ := hF
  obtain ⟨hg1, hg2, he, -, -⟩ := alg P ha hb
  unfold G at hGS; unfold K at hSKB
  rcases hθ0.lt_or_eq with hθ | hθ
  swap
  · rw [← hθ]; simp
  -- (1) fair valuation
  have h1 : o.γ * o.pay ≥ o.θ * (1 / P.a + 1 / P.b) := by
    unfold PiE K at hfair
    have hm : 0 ≤ (1 - o.γ) * (o.B - o.θ ^ 2 / P.a - o.S) :=
      mul_nonneg (by linarith) (by linarith)
    have key : o.θ * (o.γ * o.pay) - o.θ * (o.θ * (1 / P.a + 1 / P.b))
        = (1 - o.γ) * (o.B - o.θ ^ 2 / P.a - o.S) + (o.S - o.θ ^ 2 / P.b) := by
      linear_combination hfair
    have : o.θ * (o.γ * o.pay) ≥ o.θ * (o.θ * (1 / P.a + 1 / P.b)) := by
      linarith
    exact le_of_mul_le_mul_left this hθ
  -- (2) incentive compatibility, local deviation downwards
  set k := (1 - o.γ) / P.a + 1 / P.b with hk
  have hkpos : 0 < k := by
    have : 0 ≤ (1 - o.γ) / P.a := div_nonneg (by linarith) ha.le
    have : 0 < 1 / P.b := by positivity
    linarith
  set D0 := (1 - o.γ) * (2 * o.θ / P.a - o.pay) + 2 * o.θ / P.b with hD0
  have hdev : ∀ ε : ℝ, 0 < ε → ε ≤ o.θ → D0 - ε * k ≤ 0 := by
    intro ε hε hεθ
    have hfe : Feasible P o.B o.BG (o.θ - ε) o.S := by
      refine ⟨by linarith, by linarith, ?_, hSBG, ?_, le_trans (by linarith) hmin⟩
      · unfold G
        have : (o.θ - ε) ^ 2 ≤ o.θ ^ 2 := by nlinarith
        have := div_le_div_of_nonneg_right this hb.le
        linarith
      · unfold K
        have : (o.θ - ε) ^ 2 ≤ o.θ ^ 2 := by nlinarith
        have := div_le_div_of_nonneg_right this ha.le
        linarith
    have hic := hIC _ _ hfe
    have hdiff : UNE P o.γ o.B o.pay o.θ o.S - UNE P o.γ o.B o.pay (o.θ - ε) o.S
        = -ε * (D0 - ε * k) := by
      simp only [UNE, PiE, K, G, hD0, hk]; field_simp; ring
    have : 0 ≤ -ε * (D0 - ε * k) := by linarith
    by_contra hc'; push Not at hc'
    have : 0 < ε * (D0 - ε * k) := mul_pos hε hc'
    linarith
  have h2 : D0 ≤ 0 := by
    by_contra hc'; push Not at hc'
    set ε := min o.θ (D0 / (2 * k))
    have hε : 0 < ε := lt_min hθ (by positivity)
    have h := hdev ε hε (min_le_left _ _)
    have : ε * k ≤ D0 / 2 := by
      have := min_le_right o.θ (D0 / (2 * k))
      calc ε * k ≤ D0 / (2 * k) * k := mul_le_mul_of_nonneg_right this hkpos.le
        _ = D0 / 2 := by field_simp
    linarith
  have h2' : (1 - o.γ) * (o.pay - 2 * o.θ / P.a) ≥ 2 * o.θ / P.b := by
    simp only [hD0] at h2; linarith
  refine ⟨?_, fun _ => ⟨h1, h2'⟩⟩
  -- (3) combine
  set d := denE P / 2 with hd
  set e := d - 2 / P.a with hed
  have hid : (1 / P.a + 1 / P.b) * e * P.b + 2 * d = P.b * d * e := by
    have := hg1; have := hg2
    rw [← hg1]
    have hb' := hb.ne'
    have h' : (1 - gammaHat P) * e * P.b = 2 := by
      rw [hg2]; field_simp
    linear_combination (-d) * h'
  suffices hsuf : o.θ * d ≤ o.pay by
    have := mul_le_mul_of_nonneg_left hsuf hθ.le
    nlinarith
  by_contra hc'; push Not at hc'
  have hu : 0 < o.θ * (1 / P.a + 1 / P.b) := by positivity
  have hγpos : 0 < o.γ := by
    rcases hγ0.lt_or_eq with h | h
    · exact h
    · have h1' := h1
      rw [← h, zero_mul] at h1'; linarith
  -- γ d > u
  have hA : o.γ * (o.θ * d) > o.θ * (1 / P.a + 1 / P.b) := by
    have := mul_lt_mul_of_pos_left hc' hγpos
    linarith
  have hB' : (1 - o.γ) * (o.θ * e) ≥ 2 * o.θ / P.b := by
    have : (1 - o.γ) * (o.pay - 2 * o.θ / P.a) ≤ (1 - o.γ) * (o.θ * e) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      have : o.θ * e = o.θ * d - 2 * o.θ / P.a := by simp only [hed]; ring
      linarith
    linarith
  -- divide by θ
  have hA2 : o.γ * d > 1 / P.a + 1 / P.b := by
    have : o.θ * (o.γ * d) > o.θ * (1 / P.a + 1 / P.b) := by linarith
    exact lt_of_mul_lt_mul_left this hθ.le
  have hB2 : (1 - o.γ) * e ≥ 2 / P.b := by
    have : o.θ * ((1 - o.γ) * e) ≥ o.θ * (2 / P.b) := by
      have : 2 * o.θ / P.b = o.θ * (2 / P.b) := by ring
      linarith
    exact le_of_mul_le_mul_left this hθ
  have hbe : 0 < P.b * e := mul_pos hb he
  have hbd : 0 < P.b * d := by
    have : 0 < d := by linarith [show 0 < 2 / P.a from by positivity]
    positivity
  have m1 := mul_lt_mul_of_pos_right hA2 hbe
  have m2 := mul_le_mul_of_nonneg_right hB2 hbd.le
  have : 2 / P.b * (P.b * d) = 2 * d := by field_simp
  nlinarith

/-- construction: every `t ∈ (0, 1]` is implementable at pay `d t`. -/
lemma construct (P : Params) (hP : P.Standing) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∃ o : EqOutcome, o.Admissible P ∧ o.θ = t ∧ o.pay = denE P / 2 * t := by
  obtain ⟨ha, hb, hc, hD, hR, hβ0, hβ1⟩ := hP
  obtain ⟨hg1, hg2, he, hγ0, hγ1⟩ := alg P ha hb
  set d := denE P / 2 with hd
  set γ := gammaHat P
  refine ⟨⟨t ^ 2 / P.a + t ^ 2 / P.b, t ^ 2 / P.b, γ, d * t, t, t ^ 2 / P.b⟩, ?_, rfl, rfl⟩
  have hBG : Ginv P (t ^ 2 / P.b) = t := by
    unfold Ginv; rw [show P.b * (t ^ 2 / P.b) = t ^ 2 by field_simp]
    exact Real.sqrt_sq ht0.le
  have hB2 : Ginv P (P.a * (t ^ 2 / P.a + t ^ 2 / P.b) / (P.a + P.b)) = t := by
    rw [show P.a * (t ^ 2 / P.a + t ^ 2 / P.b) / (P.a + P.b) = t ^ 2 / P.b by
      field_simp; ring]
    exact hBG
  refine ⟨by positivity, by positivity, hγ0.le, hγ1.le, ?_, ?_, ?_, ?_⟩
  · refine ⟨ht0.le, ht1, le_refl _, le_refl _, ?_, ?_⟩
    · unfold K; linarith
    · rw [hBG, hB2, min_self]
  · intro θ' S' hF'
    obtain ⟨h0', h1', hG', hS', hK', -⟩ := hF'
    unfold G at hG'
    have hθt : θ' ≤ t := by
      have : θ' ^ 2 ≤ t ^ 2 := by
        have := le_trans hG' hS'
        have := (div_le_div_iff_of_pos_right hb).1 this
        exact this
      nlinarith
    simp only [UNE, PiE, K, G]
    -- key: (1-γ) d = 2(1-γ)/a + 2/b
    have hk : (1 - γ) * d = 2 * (1 - γ) / P.a + 2 / P.b := by
      have : (1 - γ) * d = (1 - γ) * (d - 2 / P.a) + 2 * (1 - γ) / P.a := by ring
      rw [this, hg2]; ring
    have hx : 0 ≤ t - θ' := by linarith
    have hγS : γ * S' ≤ γ * (t ^ 2 / P.b) := mul_le_mul_of_nonneg_left hS' hγ0.le
    have hsq : t ^ 2 - θ' ^ 2 = (t - θ') * (t + θ') := by ring
    have key : (1 - γ) * (t ^ 2 / P.a + t ^ 2 / P.b - t ^ 2 / P.a - t ^ 2 / P.b + t * (d * t))
        + (t ^ 2 / P.b - t ^ 2 / P.b)
        - ((1 - γ) * (t ^ 2 / P.a + t ^ 2 / P.b - θ' ^ 2 / P.a - S' + θ' * (d * t))
          + (S' - θ' ^ 2 / P.b))
        ≥ (t - θ') * ((1 - γ) * (t - θ') / P.a + (t - θ') / P.b) := by
      have e1 : (1 - γ) * (t ^ 2 / P.a + t ^ 2 / P.b - t ^ 2 / P.a - t ^ 2 / P.b + t * (d * t))
        + (t ^ 2 / P.b - t ^ 2 / P.b)
        - ((1 - γ) * (t ^ 2 / P.a + t ^ 2 / P.b - θ' ^ 2 / P.a - S' + θ' * (d * t))
          + (S' - θ' ^ 2 / P.b))
        = (t - θ') * t * ((1 - γ) * d) - (1 - γ) * (t ^ 2 / P.a - θ' ^ 2 / P.a)
          - (1 - γ) * (t ^ 2 / P.b) - γ * S' + θ' ^ 2 / P.b := by ring
      rw [e1, hk]
      have e2 : (t - θ') * ((1 - γ) * (t - θ') / P.a + (t - θ') / P.b)
          = (t - θ') * t * (2 * (1 - γ) / P.a + 2 / P.b) - (1 - γ) * (t ^ 2 / P.a - θ' ^ 2 / P.a)
          - (1 - γ) * (t ^ 2 / P.b) - γ * (t ^ 2 / P.b) + θ' ^ 2 / P.b := by
        field_simp; ring
      rw [e2]; linarith
    have : 0 ≤ (t - θ') * ((1 - γ) * (t - θ') / P.a + (t - θ') / P.b) := by
      apply mul_nonneg hx
      have : 0 ≤ (1 - γ) * (t - θ') / P.a := div_nonneg (mul_nonneg (by linarith) hx) ha.le
      have : 0 ≤ (t - θ') / P.b := div_nonneg hx hb.le
      linarith
    linarith
  · simp only [PiE, K]
    rw [show t ^ 2 / P.a + t ^ 2 / P.b - t ^ 2 / P.a - t ^ 2 / P.b + t * (d * t)
      = t ^ 2 * d by ring]
    rw [show γ * (t ^ 2 * d) = t ^ 2 * (γ * d) by ring, hg1]; ring
  · simp only [UNE, PiE, K, G]
    have : 0 ≤ (1 - γ) * (t ^ 2 * d) := by
      have : 0 < d := by linarith [show 0 < 2 / P.a from by positivity]
      exact mul_nonneg (by linarith) (by positivity)
    linarith [show (1 - γ) * (t ^ 2 / P.a + t ^ 2 / P.b - t ^ 2 / P.a - t ^ 2 / P.b + t * (d * t))
      + (t ^ 2 / P.b - t ^ 2 / P.b) = (1 - γ) * (t ^ 2 * d) by ring]


lemma dpos (P : Params) (hP : P.Standing) : 0 < denE P / 2 := by
  obtain ⟨ha, hb, -⟩ := hP
  obtain ⟨-, -, he, -, -⟩ := alg P ha hb
  linarith [show 0 < 2 / P.a from by positivity]

lemma upper (P : Params) (hP : P.Standing) (φ : ℝ) (o : EqOutcome) (ho : o.Admissible P) :
    UE P φ o.γ o.B o.pay o.θ o.S ≤
      o.θ * piPhi P φ - denE P / 2 * o.θ ^ 2 + P.β * (P.R - φ) * P.D := by
  rw [UE_eq P φ o ho]
  have := (pay_bound P hP o ho).1
  nlinarith

lemma br_le (P : Params) (hP : P.Standing) (φ : ℝ) (o : EqOutcome) (ho : IsManufBR_E P φ o)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t * piPhi P φ - denE P / 2 * t ^ 2 ≤ o.θ * piPhi P φ - denE P / 2 * o.θ ^ 2 := by
  obtain ⟨o', ho', hθ', hpay'⟩ := construct P hP t ht0 ht1
  have h1 := ho.2 o' ho'
  have h2 := upper P hP φ o ho.1
  rw [UE_eq P φ o' ho', hθ', hpay'] at h1
  nlinarith

lemma br_of_max (P : Params) (hP : P.Standing) (φ : ℝ) (o : EqOutcome) (ho : o.Admissible P)
    (hpay : o.pay = denE P / 2 * o.θ)
    (hmax : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      x * piPhi P φ - denE P / 2 * x ^ 2 ≤ o.θ * piPhi P φ - denE P / 2 * o.θ ^ 2) :
    IsManufBR_E P φ o := by
  refine ⟨ho, fun o' ho' => ?_⟩
  have h1 := upper P hP φ o' ho'
  have hf := ho'.2.2.2.2.1
  have h2 := hmax o'.θ hf.1 hf.2.1
  rw [UE_eq P φ o ho, hpay]
  nlinarith

end EqCoreTS

namespace EqCoreTS

lemma fixed (P : Params) (hP : P.Standing) (hWL : Lb P < Wb P) (o : EqOutcome) (φ : ℝ)
    (h : IsEquityEq P o φ) (hθ1 : o.θ < 1) :
    o.θ * (denE P - Lb P) = Wb P - Lb P ∧ φ = phiHat P o.θ := by
  have hd := dpos P hP
  obtain ⟨hbr, hex⟩ := (isEquityEq_iff P o φ).1 h
  have hφ := (lemma_A1_phiHat P hP o.θ hθ1.le φ).1 hex
  refine ⟨?_, hφ⟩
  have hθ0 : 0 ≤ o.θ := hbr.1.2.2.2.2.1.1
  obtain ⟨ha, hb, hc, hD, hR, hβ0, hβ1⟩ := hP
  have hL : 0 ≤ Lb P := by
    unfold Lb; have : 0 ≤ 1 - P.β := by linarith
    positivity
  have hπ : piPhi P φ = Wb P - Lb P + Lb P * o.θ := by
    rw [hφ]; unfold piPhi phiHat Wb Lb; field_simp; ring
  have hπpos : 0 < piPhi P φ := by rw [hπ]; nlinarith
  set d := denE P / 2 with hdd
  by_cases hlt : piPhi P φ < 2 * d
  · set t := piPhi P φ / (2 * d)
    have ht0 : 0 < t := by positivity
    have ht1 : t < 1 := by rw [div_lt_one (by positivity)]; exact hlt
    have htt : piPhi P φ = 2 * d * t := by simp only [t]; field_simp
    have := br_le P ⟨ha, hb, hc, hD, hR, hβ0, hβ1⟩ φ o hbr t ht0 ht1.le
    rw [htt] at this
    have : d * (o.θ - t) ^ 2 ≤ 0 := by nlinarith
    have : (o.θ - t) ^ 2 ≤ 0 := by
      by_contra hc'; push Not at hc'; nlinarith [mul_pos hd hc']
    have hθt : o.θ = t := by nlinarith [sq_nonneg (o.θ - t)]
    have : o.θ * denE P = piPhi P φ := by rw [htt, hθt]; simp only [hdd]; ring
    rw [hπ] at this
    linarith
  · exfalso
    push Not at hlt
    have := br_le P ⟨ha, hb, hc, hD, hR, hβ0, hβ1⟩ φ o hbr 1 one_pos le_rfl
    have : (1 - o.θ) * (piPhi P φ - d * (1 + o.θ)) ≤ 0 := by nlinarith
    have : 0 < (1 - o.θ) * (piPhi P φ - d * (1 + o.θ)) :=
      mul_pos (by linarith) (by nlinarith)
    linarith

end EqCoreTS

open EqCoreTS in
theorem solution (P : Params) (hP : P.Standing) (hWL : Lb P < Wb P) :
    (∀ (o : EqOutcome) (φ : ℝ), IsEquityEq P o φ → o.θ < 1 →
        o.θ = thetaEStar P ∧ φ = phiHat P (thetaEStar P)) ∧
      (0 < thetaEStar P → thetaEStar P < 1 → ∃ (o : EqOutcome) (φ : ℝ), IsEquityEq P o φ) := by
  have hd := dpos P hP
  refine ⟨fun o φ h hθ1 => ?_, fun h0 h1 => ?_⟩
  · obtain ⟨hfix, hφ⟩ := fixed P hP hWL o φ h hθ1
    have hne : denE P - Lb P ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hfix; linarith
    have : o.θ = thetaEStar P := by
      unfold thetaEStar; rw [eq_div_iff hne]; exact hfix
    exact ⟨this, this ▸ hφ⟩
  · set t := thetaEStar P with htdef
    have hK : 0 < Wb P - Lb P := by linarith
    have hden : 0 < denE P - Lb P := by
      have : 0 < (Wb P - Lb P) / (denE P - Lb P) := h0
      exact (div_pos_iff_of_pos_left hK).1 this
    have hfix : t * (denE P - Lb P) = Wb P - Lb P := by
      simp only [htdef, thetaEStar]; field_simp
    set φ := phiHat P t
    have hπ : piPhi P φ = 2 * (denE P / 2) * t := by
      have : piPhi P φ = Wb P - Lb P + Lb P * t := by
        obtain ⟨ha, hb, hc, -⟩ := hP
        simp only [φ]; unfold piPhi phiHat Wb Lb; field_simp; ring
      rw [this]; linarith
    obtain ⟨o, ho, hθ, hpay⟩ := construct P hP t h0 h1.le
    have hbr : IsManufBR_E P φ o := br_of_max P hP φ o ho (by rw [hpay, hθ]) fun x _ _ => by
      rw [hθ, hπ]; nlinarith [sq_nonneg (x - t)]
    refine ⟨o, φ, (isEquityEq_iff P o φ).2 ⟨hbr, ?_⟩⟩
    rw [hθ]
    exact (lemma_A1_phiHat P hP t h1.le φ).2 rfl
