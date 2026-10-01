-- Prove2me | solution 1 for ShorAlgorithms.OrderFinding.card_good_outcomes_ge
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T16:17:35.129551+00:00
-- url     : https://prove2.me/submissions/98c91cdf-62e9-4576-ba25-2f82881e1623

import Mathlib
import Definitions.Def_ShorAlgorithms_OrderFinding_yieldsOrder
open ShorAlgorithms.OrderFinding
namespace AShorGood
lemma fraction_unique (n q c : ℕ) (hnq : n ^ 2 ≤ q) (s₁ s₂ : ℚ)
    (h₁ : s₁.den < n) (h₂ : s₂.den < n)
    (hs₁ : |(c : ℚ) / q - s₁| ≤ 1 / (2 * q)) (hs₂ : |(c : ℚ) / q - s₂| ≤ 1 / (2 * q)) :
    s₁ = s₂ := by
  have hd₁ : (0 : ℚ) < s₁.den := by exact_mod_cast s₁.pos
  have hd₂ : (0 : ℚ) < s₂.den := by exact_mod_cast s₂.pos
  have hd₁n : (s₁.den : ℚ) < n := by exact_mod_cast h₁
  have hd₂n : (s₂.den : ℚ) < n := by exact_mod_cast h₂
  have hnq' : (n : ℚ)^2 ≤ q := by exact_mod_cast hnq
  have hprod : (s₁.den : ℚ) * s₂.den < q := by nlinarith
  have hq : (0 : ℚ) < q := lt_trans (mul_pos hd₁ hd₂) hprod
  have hdist : |s₁-s₂| ≤ 1/(q : ℚ) := by
    calc
      |s₁-s₂| = |((c : ℚ)/q-s₂)-((c : ℚ)/q-s₁)| := by congr 1; ring
      _ ≤ |(c : ℚ)/q-s₂|+|(c : ℚ)/q-s₁| := abs_sub _ _
      _ ≤ 1/(2*(q : ℚ))+1/(2*(q : ℚ)) := add_le_add hs₂ hs₁
      _ = 1/(q : ℚ) := by ring
  have hsmall : |s₁-s₂| * ((s₁.den : ℚ)*s₂.den) < 1 := by
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right hdist (mul_pos hd₁ hd₂).le)
    rw [one_div_mul_eq_div]
    exact (div_lt_one hq).mpr hprod
  have hident : (s₁-s₂)*((s₁.den : ℚ)*s₂.den) =
      ((s₁.num*(s₂.den : ℤ)-s₂.num*(s₁.den : ℤ) : ℤ) : ℚ) := by
    push_cast
    have hx := Rat.mul_den_eq_num s₁
    have hy := Rat.mul_den_eq_num s₂
    nlinarith
  have hint : |s₁.num*(s₂.den : ℤ)-s₂.num*(s₁.den : ℤ)| < 1 := by
    have hh : |((s₁.num*(s₂.den : ℤ)-s₂.num*(s₁.den : ℤ) : ℤ) : ℚ)| < 1 := by
      rw [← hident, abs_mul, abs_of_pos (mul_pos hd₁ hd₂)]
      exact hsmall
    exact_mod_cast hh
  apply Rat.eq_iff_mul_eq_mul.mpr
  have hzero : s₁.num*(s₂.den : ℤ)-s₂.num*(s₁.den : ℤ) = 0 := by
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hint
    omega
  exact sub_eq_zero.mp hzero

noncomputable def near (q r d : ℕ) : ℕ := ⌊(q : ℝ) * d / r + 1 / 2⌋₊

lemma near_error (q r d : ℕ) : |(near q r d : ℝ) - (q : ℝ) * d / r| ≤ 1 / 2 := by
  have hl := Nat.floor_le (show 0 ≤ (q : ℝ) * d / r + 1 / 2 by positivity)
  have hu := Nat.lt_floor_add_one ((q : ℝ) * d / r + 1 / 2)
  change |(⌊(q : ℝ) * d / r + 1 / 2⌋₊ : ℝ) - (q : ℝ) * d / r| ≤ 1 / 2
  rw [abs_le]
  constructor <;> linarith

lemma near_lt {q r d : ℕ} (hr : 0 < r) (hrq : r ≤ q) (hd : d < r) : near q r d < q := by
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have hq' : (r : ℝ) ≤ q := by exact_mod_cast hrq
  have hd' : (d : ℝ) + 1 ≤ r := by exact_mod_cast hd
  have hb : (q : ℝ) * d / r ≤ q - 1 := by
    apply (div_le_iff₀ hr').mpr
    have := mul_le_mul_of_nonneg_left hd' (show 0 ≤ (q : ℝ) by positivity)
    nlinarith
  apply (Nat.floor_lt (by positivity : 0 ≤ (q : ℝ) * d / r + 1 / 2)).mpr
  linarith

lemma near_approx {q r d : ℕ} (hq : 0 < q) :
    |(near q r d : ℝ) / q - (d : ℝ) / r| ≤ 1 / (2 * q) := by
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have he : (near q r d : ℝ) / q - (d : ℝ) / r =
      ((near q r d : ℝ) - (q : ℝ) * d / r) / q := by field_simp
  rw [he, abs_div, abs_of_pos hq']
  have h := div_le_div_of_nonneg_right (near_error q r d) hq'.le
  simpa only [div_div] using h

lemma denominator {d r : ℕ} (hr : 0 < r) (hc : Nat.Coprime d r) :
    ((d : ℚ) / r).den = r := by
  simpa using Rat.den_div_eq_of_coprime (a := (d : ℤ)) (b := (r : ℤ)) (by exact_mod_cast hr) (by simpa using hc)

lemma yields {n q r c d : ℕ} (hnq : n ^ 2 ≤ q) (hr : 0 < r) (hrn : r < n)
    (hc : Nat.Coprime d r) (he : |(c : ℝ) / q - (d : ℝ) / r| ≤ 1 / (2 * q)) :
    yieldsOrder n q r c := by
  have hden := denominator hr hc
  have he' : |(c : ℚ) / q - (d : ℚ) / r| ≤ 1 / (2 * q) := by
    rw [← Rat.cast_le (K := ℝ)]
    push_cast
    exact he
  refine ⟨⟨(d : ℚ) / r, by simpa [hden] using hrn, he'⟩, ?_⟩
  intro s hs hes
  have hu := fraction_unique n q c hnq s ((d : ℚ) / r) hs (by simpa [hden] using hrn) hes he'
  simpa [hu] using hden

lemma good_card {n q r : ℕ} (hnq : n ^ 2 ≤ q) (hr : 0 < r) (hrn : r < n) :
    Nat.totient r ≤ ((Finset.univ : Finset (Fin q)).filter (fun c : Fin q => ∃ d : ℕ,
      d < r ∧ Nat.Coprime d r ∧ |((c : ℕ) : ℝ) / q - (d : ℝ) / r| ≤ 1 / (2 * q))).card := by
  classical
  have hn : 0 < n := by omega
  have hrq : r ≤ q := (hrn.le.trans (Nat.le_self_pow (by norm_num : 2 ≠ 0) n)).trans hnq
  have hq : 0 < q := hr.trans_le hrq
  let C : Fin r → Fin q := fun d => ⟨near q r d, near_lt hr hrq d.isLt⟩
  let D : Finset (Fin r) := Finset.univ.filter fun d => Nat.Coprime (d : ℕ) r
  have hD : D.card = Nat.totient r := by
    simp only [D, Nat.totient_eq_card_coprime, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_range]
    simp only [Nat.coprime_comm]
  rw [← hD]
  apply Finset.card_le_card_of_injOn C
  · intro d hd
    have hc := (Finset.mem_filter.mp hd).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, d, d.isLt, hc, near_approx hq⟩
  · intro d hd e he hde
    have hdc := (Finset.mem_filter.mp hd).2
    have hec := (Finset.mem_filter.mp he).2
    have hdapp : |((C d : ℕ) : ℚ) / q - (d : ℚ) / r| ≤ 1 / (2 * q) := by
      rw [← Rat.cast_le (K := ℝ)]
      push_cast
      exact near_approx hq
    have heapp : |((C d : ℕ) : ℚ) / q - (e : ℚ) / r| ≤ 1 / (2 * q) := by
      rw [hde]
      rw [← Rat.cast_le (K := ℝ)]
      push_cast
      exact near_approx hq
    have hu := fraction_unique n q (C d) hnq ((d : ℚ) / r) ((e : ℚ) / r)
      (by rw [denominator hr hdc]; exact hrn) (by rw [denominator hr hec]; exact hrn) hdapp heapp
    have hde' : (d : ℚ) = e := (div_left_inj' (by exact_mod_cast hr.ne' : (r : ℚ) ≠ 0)).mp hu
    apply Fin.ext
    exact_mod_cast hde'

lemma order_lt (n x : ℕ) (hn : 1 < n) (hx : Nat.Coprime x n) : orderOf (x : ZMod n) < n := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime x n).mpr hx
  rw [← hu, orderOf_units]
  calc orderOf u ≤ Fintype.card (ZMod n)ˣ := orderOf_le_card_univ
    _ = Nat.totient n := ZMod.card_units_eq_totient n
    _ < n := Nat.totient_lt n hn

lemma error_bounds {q r c d : ℕ} (hq : 0 < q) (hr : 0 < r)
    (he : |(c : ℝ) / q - (d : ℝ) / r| ≤ 1 / (2 * q)) :
    -((r : ℝ) / 2) ≤ (r : ℝ) * c - (d : ℝ) * q ∧
      (r : ℝ) * c - (d : ℝ) * q ≤ (r : ℝ) / 2 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have h := mul_le_mul_of_nonneg_right he (show 0 ≤ (q : ℝ) * r by positivity)
  have he1 : |(c : ℝ) / q - (d : ℝ) / r| * ((q : ℝ) * r) = |(r : ℝ) * c - (d : ℝ) * q| := by
    rw [← abs_of_pos (mul_pos hq' hr'), ← abs_mul]
    congr 1
    field_simp
    <;> ring
  have he2 : (1 / (2 * (q : ℝ))) * ((q : ℝ) * r) = (r : ℝ) / 2 := by field_simp
  rw [he1, he2] at h
  exact abs_le.mp h

end AShorGood

theorem solution (n x q l : ℕ) (hn : 1 < n) (hx : Nat.Coprime x n)
    (hq : q = 2 ^ l) (hnq : n ^ 2 ≤ q) (hq2 : q < 2 * n ^ 2) :
    Nat.totient (orderOf (x : ZMod n)) ≤
        ((Finset.univ : Finset (Fin q)).filter (fun c : Fin q => ∃ d : ℕ, d < orderOf (x : ZMod n) ∧
          Nat.Coprime d (orderOf (x : ZMod n)) ∧
          |((c : ℕ) : ℝ) / q - (d : ℝ) / (orderOf (x : ZMod n) : ℝ)| ≤ 1 / (2 * q))).card ∧
    ((Finset.range (orderOf (x : ZMod n))).image (fun k : ℕ => (x : ZMod n) ^ k)).card =
        orderOf (x : ZMod n) ∧
    orderOf (x : ZMod n) * Nat.totient (orderOf (x : ZMod n)) ≤
        (((Finset.univ : Finset (Fin q)).filter (fun c : Fin q => ∃ d : ℕ, d < orderOf (x : ZMod n) ∧
          Nat.Coprime d (orderOf (x : ZMod n)) ∧
          |((c : ℕ) : ℝ) / q - (d : ℝ) / (orderOf (x : ZMod n) : ℝ)| ≤ 1 / (2 * q))) ×ˢ
          ((Finset.range (orderOf (x : ZMod n))).image (fun k : ℕ => (x : ZMod n) ^ k))).card ∧
    ∀ c : Fin q, (∃ d : ℕ, d < orderOf (x : ZMod n) ∧ Nat.Coprime d (orderOf (x : ZMod n)) ∧
          |((c : ℕ) : ℝ) / q - (d : ℝ) / (orderOf (x : ZMod n) : ℝ)| ≤ 1 / (2 * q)) →
      yieldsOrder n q (orderOf (x : ZMod n)) (c : ℕ) ∧
        ∃ d : ℤ,
          -((orderOf (x : ZMod n) : ℝ) / 2) ≤
            (orderOf (x : ZMod n) : ℝ) * ((c : ℕ) : ℝ) - (d : ℝ) * (q : ℝ) ∧
          (orderOf (x : ZMod n) : ℝ) * ((c : ℕ) : ℝ) - (d : ℝ) * (q : ℝ) ≤
            (orderOf (x : ZMod n) : ℝ) / 2  := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  have hxfin : IsOfFinOrder (x : ZMod n) := ((ZMod.isUnit_iff_coprime x n).mpr hx).isOfFinOrder
  have hrn := AShorGood.order_lt n x hn hx
  have hcount := AShorGood.good_card hnq hxfin.orderOf_pos hrn
  have himg : ((Finset.range (orderOf (x : ZMod n))).image (fun k : ℕ => (x : ZMod n) ^ k)).card =
      orderOf (x : ZMod n) := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb he
    exact pow_injOn_Iio_orderOf (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) he
  refine ⟨hcount, himg, ?_, ?_⟩
  · rw [Finset.card_product, himg]
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (orderOf (x : ZMod n)) hcount
  · intro c hc
    obtain ⟨d, hd, hdco, he⟩ := hc
    refine ⟨AShorGood.yields hnq hxfin.orderOf_pos hrn hdco he, (d : ℤ), ?_⟩
    have hqpos : 0 < q := lt_of_lt_of_le (by positivity : 0 < n ^ 2) hnq
    simpa using AShorGood.error_bounds hqpos hxfin.orderOf_pos he
