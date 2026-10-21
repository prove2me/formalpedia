-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P03.lemma18_filter
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T11:22:59.061431+00:00
-- url     : https://prove2.me/submissions/fc72696e-c79c-4749-bc6f-815e3a8f3281

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate ComplexOrder

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace


set_option maxHeartbeats 1600000 in
lemma g58a_perP (e η α β x b : ℝ) (he : 0 < e) (hη : 0 < η) (ha : |α| ≤ η) (hb0 : 0 ≤ β)
    (hb1 : β ≤ 1) (hx : |x - α * β| < η * e) (hbe : |b - β| < e) :
    β * |sparseFilter e η x b - α| ^ 2 ≤ 6 * α ^ 2 ∧
    β * |sparseFilter e η x b - α| ^ 2 ≤ 9 * η ^ 2 * e ∧
    (β * |sparseFilter e η x b - α| ^ 2) ^ 2 ≤ 36 * (α ^ 2 * (η ^ 2 * e)) := by
  have hα2 : α ^ 2 ≤ η ^ 2 := by
    have := abs_nonneg α; nlinarith [sq_abs α]
  have hbe' := abs_lt.mp hbe
  have hx' := abs_lt.mp hx
  have hA0 : 0 ≤ |α| := abs_nonneg α
  have hαβ : |α| * β ≤ |x| + η * e := by
    have : |α * β| ≤ |x| + |x - α * β| := by
      have := abs_sub_abs_le_abs_sub (α * β) x
      rw [abs_sub_comm] at this; linarith [abs_sub_comm x (α * β)]
    rw [abs_mul, abs_of_nonneg hb0] at this; linarith
  unfold sparseFilter
  by_cases h1 : b ≤ 2 * e
  · simp only [if_pos h1, zero_sub, abs_neg, sq_abs]
    have hβ3 : β ≤ 3 * e := by linarith
    refine ⟨by nlinarith [sq_nonneg α], by nlinarith [sq_nonneg α], ?_⟩
    have l1 : β * α ^ 2 ≤ α ^ 2 := by nlinarith [sq_nonneg α]
    have l2 : β * α ^ 2 ≤ 3 * (η ^ 2 * e) := by nlinarith [sq_nonneg α]
    have l0 : 0 ≤ β * α ^ 2 := by positivity
    nlinarith
  · simp only [if_neg h1]
    push Not at h1
    have hb : 0 < b := by linarith
    have hsb := Real.sqrt_pos.mpr hb
    have hse := Real.sqrt_pos.mpr he
    have hsb2 := Real.sq_sqrt hb.le
    have hse2 := Real.sq_sqrt he.le
    set sb := Real.sqrt b
    set se := Real.sqrt e
    by_cases h2 : |x| / sb ≤ 2 * η * se
    · simp only [if_pos h2, zero_sub, abs_neg, sq_abs]
      rw [div_le_iff₀ hsb] at h2
      have hL9 : β * α ^ 2 ≤ 9 * η ^ 2 * e := by
        by_cases h9 : β ≤ 9 * e
        · nlinarith [sq_nonneg α]
        · push Not at h9
          have hβpos : 0 < β := by linarith
          have k1 : |α| * β ≤ η * se * (2 * sb + se) := by nlinarith
          have k2 : (2 * sb + se) ^ 2 ≤ 9 * β := by nlinarith [sq_nonneg (sb - 2 * se)]
          have k3 : (|α| * β) ^ 2 ≤ (η * se) ^ 2 * (2 * sb + se) ^ 2 := by
            rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) k1 2
          have k4 : β * (β * α ^ 2) ≤ β * (9 * η ^ 2 * e) := by
            have : (|α| * β) ^ 2 = β * (β * α ^ 2) := by rw [mul_pow, sq_abs]; ring
            rw [← this]
            calc (|α| * β) ^ 2 ≤ (η * se) ^ 2 * (2 * sb + se) ^ 2 := k3
              _ ≤ (η * se) ^ 2 * (9 * β) := by gcongr
              _ = β * (9 * η ^ 2 * e) := by rw [mul_pow, hse2]; ring
          exact le_of_mul_le_mul_left k4 hβpos
      refine ⟨by nlinarith [sq_nonneg α], hL9, ?_⟩
      have l1 : β * α ^ 2 ≤ α ^ 2 := by nlinarith [sq_nonneg α]
      have l0 : 0 ≤ β * α ^ 2 := by positivity
      nlinarith
    · simp only [if_neg h2]
      push Not at h2
      rw [lt_div_iff₀ hsb] at h2
      have hnum : |x - α * b| ≤ 2 * η * e := by
        have e1 : x - α * b = (x - α * β) + α * (β - b) := by ring
        have e2 : |α * (β - b)| ≤ η * e := by
          rw [abs_mul, abs_sub_comm]
          exact mul_le_mul ha hbe.le (abs_nonneg _) hη.le
        rw [e1]
        calc |x - α * β + α * (β - b)| ≤ |x - α * β| + |α * (β - b)| := abs_add_le _ _
          _ ≤ η * e + η * e := add_le_add hx.le e2
          _ = 2 * η * e := by ring
      have hfa : |x / b - α| ≤ 2 * η * e / b := by
        rw [show x / b - α = (x - α * b) / b by field_simp, abs_div, abs_of_pos hb]
        exact div_le_div_of_nonneg_right hnum hb.le
      have hfa2 : |x / b - α| ^ 2 ≤ (2 * η * e / b) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hfa 2
      have hL : β * |x / b - α| ^ 2 ≤ β * (2 * η * e / b) ^ 2 := mul_le_mul_of_nonneg_left hfa2 hb0
      have hL3 : β * |x / b - α| ^ 2 ≤ 3 * (η ^ 2 * e) := by
        refine hL.trans ?_
        rw [div_pow, mul_div_assoc', div_le_iff₀ (by positivity)]
        have : β ≤ 3 / 2 * b := by linarith
        have hbe2 : β * e ≤ 3 / 4 * b ^ 2 := by nlinarith
        calc β * (2 * η * e) ^ 2 = 4 * (η ^ 2 * e) * (β * e) := by ring
          _ ≤ 4 * (η ^ 2 * e) * (3 / 4 * b ^ 2) := by gcongr
          _ = 3 * (η ^ 2 * e) * b ^ 2 := by ring
      have hseb : se ≤ sb := Real.sqrt_le_sqrt (by linarith)
      have hL6 : β * |x / b - α| ^ 2 ≤ 6 * α ^ 2 := by
        refine hL.trans ?_
        by_cases hβ0 : β = 0
        · rw [hβ0]; nlinarith [sq_nonneg α]
        have hβpos : 0 < β := lt_of_le_of_ne hb0 (Ne.symm hβ0)
        have hxl : |x| ≤ |α| * β + η * e := by
          have := abs_sub_abs_le_abs_sub x (α * β)
          rw [abs_mul, abs_of_nonneg hb0] at this; linarith
        have k1 : η * se * (2 * sb - se) ≤ |α| * β := by
          have : η * se * (2 * sb - se) = 2 * η * se * sb - η * e := by rw [← hse2]; ring
          rw [this]; linarith
        have k1' : 0 ≤ η * se * (2 * sb - se) := by
          have : 0 ≤ 2 * sb - se := by linarith
          positivity
        have k2 : (η * se * (2 * sb - se)) ^ 2 ≤ (|α| * β) ^ 2 := pow_le_pow_left₀ k1' k1 2
        have k3 : sb ^ 2 ≤ (2 * sb - se) ^ 2 := pow_le_pow_left₀ hsb.le (by linarith) 2
        have k4 : 2 * β ^ 3 * e ≤ 3 * b ^ 3 := by
          have h3 : β ^ 3 ≤ β ^ 2 := by
            calc β ^ 3 = β ^ 2 * β := by ring
              _ ≤ β ^ 2 * 1 := by gcongr
              _ = β ^ 2 := by ring
          have hb2 : β ^ 2 ≤ (3 / 2 * b) ^ 2 := pow_le_pow_left₀ hb0 (by linarith) 2
          calc 2 * β ^ 3 * e ≤ 2 * β ^ 2 * e := by gcongr
            _ ≤ 2 * (3 / 2 * b) ^ 2 * e := by gcongr
            _ ≤ 2 * (3 / 2 * b) ^ 2 * (b / 2) := by gcongr; linarith
            _ ≤ 3 * b ^ 3 := by nlinarith [pow_pos hb 3]
        rw [div_pow, mul_div_assoc', div_le_iff₀ (by positivity)]
        have k5 : η ^ 2 * e * b ≤ α ^ 2 * β ^ 2 := by
          have : (η * se * (2 * sb - se)) ^ 2 = η ^ 2 * e * (2 * sb - se) ^ 2 := by
            rw [mul_pow, mul_pow, hse2]
          have h' : (|α| * β) ^ 2 = α ^ 2 * β ^ 2 := by rw [mul_pow, sq_abs]
          rw [this, h'] at k2
          calc η ^ 2 * e * b = η ^ 2 * e * sb ^ 2 := by rw [hsb2]
            _ ≤ η ^ 2 * e * (2 * sb - se) ^ 2 := by gcongr
            _ ≤ _ := k2
        have : β ^ 2 * (β * (2 * η * e) ^ 2) ≤ β ^ 2 * (6 * α ^ 2 * b ^ 2) := by
          have e1 : β ^ 2 * (β * (2 * η * e) ^ 2) = 2 * (2 * β ^ 3 * e) * (η ^ 2 * e) := by ring
          have e2 : β ^ 2 * (6 * α ^ 2 * b ^ 2) = 6 * b ^ 2 * (α ^ 2 * β ^ 2) := by ring
          rw [e1, e2]
          calc 2 * (2 * β ^ 3 * e) * (η ^ 2 * e) ≤ 2 * (3 * b ^ 3) * (η ^ 2 * e) := by gcongr
            _ = 6 * b ^ 2 * (η ^ 2 * e * b) := by ring
            _ ≤ 6 * b ^ 2 * (α ^ 2 * β ^ 2) := by gcongr
        exact le_of_mul_le_mul_left this (by positivity)
      refine ⟨hL6, by nlinarith [sq_nonneg η], ?_⟩
      have l0 : 0 ≤ β * |x / b - α| ^ 2 := by positivity
      calc (β * |x / b - α| ^ 2) ^ 2 = (β * |x / b - α| ^ 2) * (β * |x / b - α| ^ 2) := sq _
        _ ≤ (6 * α ^ 2) * (3 * (η ^ 2 * e)) := mul_le_mul hL6 hL3 l0 (by positivity)
        _ ≤ 36 * (α ^ 2 * (η ^ 2 * e)) := by nlinarith [sq_nonneg α, sq_nonneg η]

lemma g58a_rpow_bound (e η α r L : ℝ) (he : 0 < e) (hη : 0 < η) (hr1 : 1 ≤ r) (hr2 : r < 2)
    (h1 : L ≤ 6 * α ^ 2) (h2 : L ^ 2 ≤ 36 * (α ^ 2 * (η ^ 2 * e))) :
    L ≤ 6 * (|α| ^ r * η ^ (2 - r) * e ^ (1 - r / 2)) := by
  set c := η * Real.sqrt e with hc
  have hse := Real.sqrt_pos.mpr he
  have hcpos : 0 < c := by positivity
  have hc2 : c ^ 2 = η ^ 2 * e := by rw [hc, mul_pow, Real.sq_sqrt he.le]
  have hE : e ^ (1 - r / 2) = Real.sqrt e ^ (2 - r) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul he.le]; congr 1; ring
  set t := |α| / c with ht
  have ht0 : 0 ≤ t := by positivity
  have hα : |α| = t * c := by rw [ht]; field_simp
  have hR : |α| ^ r * η ^ (2 - r) * e ^ (1 - r / 2) = t ^ r * c ^ 2 := by
    rw [hE, mul_assoc, ← Real.mul_rpow hη.le hse.le, ← hc, hα, Real.mul_rpow ht0 hcpos.le, mul_assoc,
      ← Real.rpow_add hcpos]
    norm_num
  rw [hR]
  have hL1 : L ≤ 6 * (t ^ 2 * c ^ 2) := by
    have : α ^ 2 = t ^ 2 * c ^ 2 := by rw [← sq_abs, hα, mul_pow]
    rw [← this]; exact h1
  have hL2 : L ≤ 6 * (t * c ^ 2) := by
    have : 36 * (α ^ 2 * (η ^ 2 * e)) = (6 * (t * c ^ 2)) ^ 2 := by
      rw [← hc2, ← sq_abs α, hα]; ring
    rw [this] at h2
    have h0 : 0 ≤ 6 * (t * c ^ 2) := by positivity
    exact abs_le_of_sq_le_sq' h2 h0 |>.2
  rcases le_total t 1 with h | h
  · have : t ^ (2 : ℝ) ≤ t ^ r := by
      rcases ht0.lt_or_eq with h0 | h0
      · exact Real.rpow_le_rpow_of_exponent_ge h0 h hr2.le
      · rw [← h0, Real.zero_rpow (by norm_num), Real.zero_rpow (by linarith)]
    rw [Real.rpow_two] at this
    calc L ≤ 6 * (t ^ 2 * c ^ 2) := hL1
      _ ≤ 6 * (t ^ r * c ^ 2) := by gcongr
  · have : t ^ (1 : ℝ) ≤ t ^ r := Real.rpow_le_rpow_of_exponent_le h hr1
    rw [Real.rpow_one] at this
    calc L ≤ 6 * (t * c ^ 2) := hL2
      _ ≤ 6 * (t ^ r * c ^ 2) := by gcongr

theorem solution (n : ℕ) (S : Finset ((Fin n → Fin 4))) (e eta A r : ℝ)
    (he : 0 < e) (heta : 0 < eta) (hA : 0 < A) (hr1 : 1 ≤ r) (hr2 : r < 2)
    (alpha beta xhat bhat : (Fin n → Fin 4) → ℝ)
    (ha : ∀ P ∈ S, |alpha P| ≤ eta)
    (hb : ∀ P ∈ S, 0 ≤ beta P ∧ beta P ≤ 1)
    (hmass : ∑ P ∈ S, Real.rpow |alpha P| r ≤ Real.rpow A r)
    (hx : ∀ P ∈ S, |xhat P - alpha P * beta P| < eta * e)
    (hbe : ∀ P ∈ S, |bhat P - beta P| < e) :
    (∑ P ∈ S, beta P * |sparseFilter e eta (xhat P) (bhat P) - alpha P| ^ 2) ≤
      6 * Real.rpow A r * Real.rpow eta (2 - r) * Real.rpow e (1 - r / 2) ∧
    ∀ P ∈ S, beta P * |sparseFilter e eta (xhat P) (bhat P) - alpha P| ^ 2 ≤
      9 * eta ^ 2 * e := by
  have hP := fun P (hPS : P ∈ S) => g58a_perP e eta (alpha P) (beta P) (xhat P) (bhat P) he heta
    (ha P hPS) (hb P hPS).1 (hb P hPS).2 (hx P hPS) (hbe P hPS)
  refine ⟨?_, fun P hPS => (hP P hPS).2.1⟩
  simp only [Real.rpow_eq_pow] at hmass ⊢
  calc (∑ P ∈ S, beta P * |sparseFilter e eta (xhat P) (bhat P) - alpha P| ^ 2)
      ≤ ∑ P ∈ S, 6 * (|alpha P| ^ r * eta ^ (2 - r) * e ^ (1 - r / 2)) :=
        Finset.sum_le_sum fun P hPS => g58a_rpow_bound e eta (alpha P) r _ he heta hr1 hr2
          (hP P hPS).1 (hP P hPS).2.2
    _ = 6 * (eta ^ (2 - r) * e ^ (1 - r / 2)) * ∑ P ∈ S, |alpha P| ^ r := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ 6 * (eta ^ (2 - r) * e ^ (1 - r / 2)) * A ^ r := by gcongr
    _ = 6 * A ^ r * eta ^ (2 - r) * e ^ (1 - r / 2) := by ring

end
