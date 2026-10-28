-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P15.eq55to56NoNewConstraint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T14:07:52.299832+00:00
-- url     : https://prove2.me/submissions/411c41b1-f10c-4abd-a76a-90c6ab2a551e

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

open Real Set

namespace X8E55

open QAlgorithms.Papers.Independent.Support50.P15

lemma binE (p : ℝ) : Real.binEntropy p = -(p * Real.log p) - (1 - p) * Real.log (1 - p) := by
  unfold Real.binEntropy; rw [Real.log_inv, Real.log_inv]; ring

lemma h_zero (d : ℕ) : degenerateSpectrumEntropy d 0 = 0 := by
  simp [degenerateSpectrumEntropy]

lemma m_facts {d : ℕ} (hd : 2 ≤ d) : 0 < massLimit d ∧ massLimit d < 1 ∧ 1 - massLimit d = 1 / d := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold massLimit
  refine ⟨div_pos (by linarith) (by linarith), (div_lt_one (by linarith)).2 (by linarith), ?_⟩
  field_simp; ring

lemma h_m {d : ℕ} (hd : 2 ≤ d) : degenerateSpectrumEntropy d (massLimit d) = Real.log d := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨_, _, h1⟩ := m_facts hd
  unfold degenerateSpectrumEntropy
  rw [binE, h1]
  have hm : massLimit d = ((d : ℝ) - 1) / d := rfl
  rw [hm, Real.log_div (by linarith) (by linarith), one_div, Real.log_inv]
  field_simp; ring

lemma h_cont (d : ℕ) : Continuous (degenerateSpectrumEntropy d) := by
  unfold degenerateSpectrumEntropy; fun_prop

/-- `log (1/(1-r)) ≤ h(r)` on `[0,m]`, strictly inside. -/
lemma slack {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ massLimit d) :
    degenerateSpectrumEntropy d r - Real.log (1 / (1 - r)) =
      r * Real.log ((1 - r) * ((d : ℝ) - 1) / r) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨_, hm1, _⟩ := m_facts hd
  have hr1 : 0 < 1 - r := by linarith
  unfold degenerateSpectrumEntropy
  rw [binE, one_div, Real.log_inv]
  rcases h0.eq_or_lt with h | h
  · subst h; simp
  · have hd1 : (0:ℝ) < (d:ℝ) - 1 := by linarith
    rw [Real.log_div (mul_pos hr1 hd1).ne' h.ne', Real.log_mul hr1.ne' hd1.ne']
    ring

lemma slack_nonneg {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ massLimit d) :
    Real.log (1 / (1 - r)) ≤ degenerateSpectrumEntropy d r := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have e := slack hd h0 h1
  rcases h0.eq_or_lt with h | h
  · subst h; simp [h_zero]
  have hm : massLimit d = ((d : ℝ) - 1) / d := rfl
  have hle : r * d ≤ (d : ℝ) - 1 := by rw [hm, le_div_iff₀ (by linarith)] at h1; linarith
  have : 0 ≤ Real.log ((1 - r) * ((d : ℝ) - 1) / r) := by
    apply Real.log_nonneg; rw [le_div_iff₀ h]; nlinarith
  nlinarith [mul_nonneg h.le this]

lemma slack_pos {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (h0 : 0 < r) (h1 : r < massLimit d) :
    Real.log (1 / (1 - r)) < degenerateSpectrumEntropy d r := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have e := slack hd h0.le h1.le
  have hm : massLimit d = ((d : ℝ) - 1) / d := rfl
  have hle : r * d < (d : ℝ) - 1 := by rw [hm, lt_div_iff₀ (by linarith)] at h1; linarith
  have : 0 < Real.log ((1 - r) * ((d : ℝ) - 1) / r) := by
    apply Real.log_pos; rw [lt_div_iff₀ h0]; nlinarith
  nlinarith [mul_pos h0 this]

lemma h_nonneg {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ massLimit d) :
    0 ≤ degenerateSpectrumEntropy d r := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨_, hm1, _⟩ := m_facts hd
  unfold degenerateSpectrumEntropy
  have := Real.binEntropy_nonneg h0 (by linarith)
  have : 0 ≤ Real.log ((d : ℝ) - 1) := Real.log_nonneg (by linarith)
  positivity

/-- `log x > 1 - 1/x` for `x ≠ 1`. -/
lemma log_gt {x : ℝ} (hx : 0 < x) (h1 : x ≠ 1) : 1 - 1 / x < Real.log x := by
  have := Real.log_lt_sub_one_of_pos (inv_pos.2 hx) (by
    intro h; apply h1; have := congrArg (·⁻¹) h; simpa using this)
  rw [Real.log_inv] at this; rw [one_div]; linarith

lemma h_lt {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (h0 : 0 ≤ r) (h1 : r < massLimit d) :
    degenerateSpectrumEntropy d r < Real.log d := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hm : massLimit d = ((d : ℝ) - 1) / d := rfl
  have hle : r * d < (d : ℝ) - 1 := by rw [hm, lt_div_iff₀ (by linarith)] at h1; linarith
  have hr1 : 0 < 1 - r := by nlinarith
  have hd0 : (0 : ℝ) < d := by linarith
  -- first term: (1-r) log(d(1-r)) > (1-r) - 1/d
  have hx : 0 < (d : ℝ) * (1 - r) := by positivity
  have hx1 : (d : ℝ) * (1 - r) ≠ 1 := by intro h; nlinarith
  have t1 := log_gt hx hx1
  have t1' : (1 - r) - 1 / d < (1 - r) * Real.log ((d : ℝ) * (1 - r)) := by
    have := mul_lt_mul_of_pos_left t1 hr1
    have e : (1 - r) * (1 - 1 / ((d : ℝ) * (1 - r))) = (1 - r) - 1 / d := by field_simp
    linarith
  -- second term: r log(d r/(d-1)) ≥ r - (d-1)/d
  have t2 : r - ((d : ℝ) - 1) / d ≤ r * Real.log ((d : ℝ) * r / ((d : ℝ) - 1)) := by
    rcases h0.eq_or_lt with h | h
    · subst h; simp; exact div_nonneg (by linarith) hd0.le
    · have hy : 0 < (d : ℝ) * r / ((d : ℝ) - 1) := by
        apply div_pos (by positivity) (by linarith)
      have := Real.one_sub_inv_le_log_of_pos hy
      have := mul_le_mul_of_nonneg_left this h.le
      have e : r * (1 - ((d : ℝ) * r / ((d : ℝ) - 1))⁻¹) = r - ((d : ℝ) - 1) / d := by
        field_simp
      linarith
  have e : Real.log d - degenerateSpectrumEntropy d r =
      (1 - r) * Real.log ((d : ℝ) * (1 - r)) + r * Real.log ((d : ℝ) * r / ((d : ℝ) - 1)) := by
    unfold degenerateSpectrumEntropy
    rw [binE, Real.log_mul hd0.ne' hr1.ne']
    rcases h0.eq_or_lt with h | h
    · subst h; simp
    · rw [Real.log_div (by positivity) (by linarith), Real.log_mul hd0.ne' h.ne']
      ring
  have : (1 - r) - 1 / d + (r - ((d : ℝ) - 1) / d) = 0 := by field_simp; ring
  linarith

lemma h_le {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ massLimit d) :
    degenerateSpectrumEntropy d r ≤ Real.log d := by
  rcases h1.lt_or_eq with h | h
  · exact (h_lt hd h0 h).le
  · rw [h, h_m hd]

end X8E55


open Real Set

namespace X8E55

open QAlgorithms.Papers.Independent.Support50.P15

lemma kl_ge {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) : (((p - q : ℝ)) : EReal) ≤ klTerm p q := by
  unfold klTerm
  by_cases h0 : p = 0
  · subst h0; simp only [if_true]; exact_mod_cast (by linarith : (0 : ℝ) - q ≤ 0)
  rw [if_neg h0]
  by_cases h1 : q = 0
  · rw [if_pos h1]; exact le_top
  rw [if_neg h1]
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm h0)
  have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm h1)
  apply EReal.coe_le_coe_iff.2
  have := Real.one_sub_inv_le_log_of_pos (div_pos hp' hq')
  have := mul_le_mul_of_nonneg_left this hp
  have e : p * (1 - (p / q)⁻¹) = p - q := by field_simp
  linarith

lemma br_nonneg {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (0 : EReal) ≤ binaryRelative s r := by
  unfold binaryRelative
  have h1 := kl_ge hs0 hr0
  have h2 := kl_ge (by linarith : (0:ℝ) ≤ 1 - s) (by linarith : (0:ℝ) ≤ 1 - r)
  have := add_le_add h1 h2
  rw [← EReal.coe_add] at this
  have e : s - r + (1 - s - (1 - r)) = 0 := by ring
  rw [e] at this
  exact_mod_cast this

lemma br_zero {r : ℝ} (hr : r < 1) :
    binaryRelative 0 r = ((Real.log (1 / (1 - r)) : ℝ) : EReal) := by
  unfold binaryRelative klTerm
  have : (1 : ℝ) - r ≠ 0 := by linarith
  simp [this]

lemma feas_zero {d : ℕ} (hd : 2 ≤ d) {delta : ℝ} (hdelta : delta ∈ Icc (-Real.log d) 0) :
    ∃ r ∈ Icc 0 (massLimit d), entropyDifferenceFeasible d delta 0 r ∧
      degenerateSpectrumEntropy d r = -delta := by
  obtain ⟨hm0, hm1, _⟩ := m_facts hd
  have hivt := intermediate_value_Icc hm0.le (h_cont d).continuousOn
  rw [h_zero, h_m hd] at hivt
  obtain ⟨r, hr, hrv⟩ := hivt (show -delta ∈ Icc 0 (Real.log d) from ⟨by linarith [hdelta.2], by linarith [hdelta.1]⟩)
  refine ⟨r, hr, ⟨⟨le_refl _, hm0.le⟩, hr, ?_⟩, hrv⟩
  rw [h_zero, hrv]; ring

lemma part1 {d : ℕ} (hd : 2 ≤ d) {delta : ℝ} (hdelta : delta ∈ Icc (-Real.log d) 0) :
    ∃ r ∈ Icc 0 (massLimit d), degenerateSpectrumEntropy d r = -delta ∧
      tightBound d delta ≤ ((Real.log (1 / (1 - r)) : ℝ) : EReal) := by
  obtain ⟨_, hm1, _⟩ := m_facts hd
  obtain ⟨r, hr, hf, hv⟩ := feas_zero hd hdelta
  refine ⟨r, hr, hv, ?_⟩
  rw [← br_zero (by linarith [hr.2])]
  exact sInf_le ⟨0, r, hf, rfl⟩

lemma lower_zero {d : ℕ} (hd : 2 ≤ d) : (0 : EReal) ≤ tightBound d 0 := by
  obtain ⟨_, hm1, _⟩ := m_facts hd
  apply le_sInf
  rintro _ ⟨s, r, ⟨hs, hr, _⟩, rfl⟩
  exact br_nonneg hs.1 (by linarith [hs.2]) hr.1 (by linarith [hr.2])

lemma lower_log {d : ℕ} (hd : 2 ≤ d) :
    ((Real.log d : ℝ) : EReal) ≤ tightBound d (-Real.log d) := by
  obtain ⟨hm0, hm1, hm2⟩ := m_facts hd
  apply le_sInf
  rintro _ ⟨s, r, ⟨hs, hr, he⟩, rfl⟩
  have hs0 := h_nonneg hd hs.1 hs.2
  have hrle := h_le hd hr.1 hr.2
  have hhs : degenerateSpectrumEntropy d s = 0 := by linarith
  have hhr : degenerateSpectrumEntropy d r = Real.log d := by linarith
  have hr' : r = massLimit d := by
    by_contra hne
    have := h_lt hd hr.1 (lt_of_le_of_ne hr.2 hne); linarith
  have hs' : s = 0 := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hb := Real.binEntropy_nonneg hs.1 (by linarith [hs.2])
    have hl : 0 ≤ s * Real.log ((d : ℝ) - 1) := mul_nonneg hs.1 (Real.log_nonneg (by linarith))
    unfold degenerateSpectrumEntropy at hhs
    have : Real.binEntropy s = 0 := by linarith
    rcases Real.binEntropy_eq_zero.1 this with h | h
    · exact h
    · linarith [hs.2]
  subst hs'; rw [hr', br_zero hm1, hm2]
  apply le_of_eq; congr 1
  rw [one_div_one_div]

theorem x8_main {d : ℕ} (hd : 2 ≤ d) (delta : ℝ)
    (hdelta : delta ∈ Set.Icc (-Real.log d) 0) :
    tightBound d delta ≤ (-delta : ℝ) ∧
    (tightBound d delta = (-delta : ℝ) ↔ delta = -Real.log d ∨ delta = 0) ∧
    (delta ∈ Set.Ioo (-Real.log d) 0 → tightBound d delta < (-delta : ℝ)) := by
  obtain ⟨r, hr, hv, hle⟩ := part1 hd hdelta
  have p1 : tightBound d delta ≤ (-delta : ℝ) :=
    hle.trans (EReal.coe_le_coe_iff.2 (hv ▸ slack_nonneg hd hr.1 hr.2))
  have p3 : delta ∈ Set.Ioo (-Real.log d) 0 → tightBound d delta < (-delta : ℝ) := by
    intro hI
    have hr0 : r ≠ 0 := by
      rintro rfl; rw [h_zero] at hv; linarith [hI.2]
    have hrm : r ≠ massLimit d := by
      rintro rfl; rw [h_m hd] at hv; linarith [hI.1]
    exact hle.trans_lt (EReal.coe_lt_coe_iff.2
      (hv ▸ slack_pos hd (lt_of_le_of_ne hr.1 (Ne.symm hr0)) (lt_of_le_of_ne hr.2 hrm)))
  refine ⟨p1, ⟨fun heq => ?_, fun h => ?_⟩, p3⟩
  · by_contra hcon
    push Not at hcon
    have hI : delta ∈ Set.Ioo (-Real.log d) 0 :=
      ⟨lt_of_le_of_ne hdelta.1 (Ne.symm hcon.1), lt_of_le_of_ne hdelta.2 hcon.2⟩
    exact absurd heq (p3 hI).ne
  · apply le_antisymm p1
    rcases h with h | h
    · subst h; rw [neg_neg]; exact lower_log hd
    · subst h; simpa using lower_zero hd

end X8E55

open QAlgorithms.Papers.Independent.Support50.P15 in
theorem solution {d : ℕ} (hd : 2 ≤ d) (delta : ℝ)
    (hdelta : delta ∈ Set.Icc (-Real.log d) 0) :
    tightBound d delta ≤ (-delta : ℝ) ∧
    (tightBound d delta = (-delta : ℝ) ↔ delta = -Real.log d ∨ delta = 0) ∧
    (delta ∈ Set.Ioo (-Real.log d) 0 → tightBound d delta < (-delta : ℝ)) :=
  X8E55.x8_main hd delta hdelta
