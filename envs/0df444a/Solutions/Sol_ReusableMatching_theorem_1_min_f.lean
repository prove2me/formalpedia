-- Prove2me | solution 1 for ReusableMatching.theorem_1_min_f
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:34:14.902634+00:00
-- url     : https://prove2.me/submissions/c2915d6b-253e-4551-9b0e-0b787c96013b

import Mathlib
import Definitions.Def_ReusableMatching_fBound

namespace Aux_ReusableMatching_minf

lemma exp_hi (x : ℝ) (hx : |x| ≤ 1) :
    Real.exp x ≤ (∑ m ∈ Finset.range 12, x ^ m / (m.factorial : ℝ))
      + |x| ^ 12 * ((Nat.succ 12 : ℝ) / ((Nat.factorial 12 : ℝ) * 12)) := by
  have h := Real.exp_bound hx (n := 12) (by norm_num)
  have := (abs_le.1 h).2
  push_cast at this ⊢
  linarith

lemma exp_lo (x : ℝ) (hx : |x| ≤ 1) :
    (∑ m ∈ Finset.range 12, x ^ m / (m.factorial : ℝ))
      - |x| ^ 12 * ((Nat.succ 12 : ℝ) / ((Nat.factorial 12 : ℝ) * 12)) ≤ Real.exp x := by
  have h := Real.exp_bound hx (n := 12) (by norm_num)
  have := (abs_le.1 h).1
  push_cast at this ⊢
  linarith

lemma a_hi : Real.exp (-(89 / 100)) ≤ 41065576 / 10 ^ 8 := by
  refine le_trans (exp_hi _ (by rw [abs_le]; constructor <;> norm_num)) ?_
  rw [abs_of_neg (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma K_lo : 66218479 / 10 ^ 8 ≤ Real.exp (-(89 / 100 * (463158 / 1000000))) := by
  refine le_trans ?_ (exp_lo _ (by rw [abs_le]; constructor <;> norm_num))
  rw [abs_of_neg (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.factorial]

end Aux_ReusableMatching_minf

set_option maxHeartbeats 1600000 in
open ReusableMatching Aux_ReusableMatching_minf in
theorem solution (z1 z2 x : ℝ) (hz1 : 0 ≤ z1) (hz12 : z1 ≤ z2) (hz2 : z2 ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (5893 / 10000 : ℝ) < fBound (89 / 100) z1 z2 x := by
  unfold fBound G
  set β : ℝ := 89 / 100 with hβ
  set a := g β 0 with ha
  set E := g β x with hE
  set g1 := g β z1 with hg1
  set g2 := g β z2 with hg2
  have ha' : a = Real.exp (-(89 / 100)) := by
    rw [ha]; unfold g; congr 1; rw [hβ]; ring
  have hahi : a ≤ 41065576 / 10 ^ 8 := ha' ▸ a_hi
  have hapos : 0 < a := by rw [ha']; exact Real.exp_pos _
  have hEa : a ≤ E := by
    rw [ha, hE]; unfold g; apply Real.exp_le_exp.2; rw [hβ]; nlinarith
  have hE1 : E ≤ 1 := by
    rw [hE]; unfold g
    have : β * (x - 1) ≤ 0 := by rw [hβ]; nlinarith
    exact (Real.exp_le_exp.2 this).trans_eq Real.exp_zero
  have hg2a : a ≤ g2 := by
    rw [ha, hg2]; unfold g; apply Real.exp_le_exp.2; rw [hβ]; nlinarith
  -- crux
  have hcrux : β * (5893 / 10000) < g2 - a + (1 - z2) * (1 - a) := by
    set u0 : ℝ := 463158 / 1000000 with hu0
    set K := Real.exp (-(β * u0)) with hK
    have hKlo : 66218479 / 10 ^ 8 ≤ K := by rw [hK, hβ, hu0]; exact K_lo
    have hsplit : g2 = K * Real.exp (-(β * ((1 - z2) - u0))) := by
      rw [hg2, hK]; unfold g; rw [← Real.exp_add]; congr 1; ring
    have htan : 1 - β * ((1 - z2) - u0) ≤ Real.exp (-(β * ((1 - z2) - u0))) := by
      have := Real.add_one_le_exp (-(β * ((1 - z2) - u0))); linarith
    have hpos1 : 0 < 1 - β * ((1 - z2) - u0) := by rw [hβ, hu0]; nlinarith
    have hKpos : 0 < K := Real.exp_pos _
    have h1 : K * (1 - β * ((1 - z2) - u0)) ≤ g2 := by
      rw [hsplit]; exact mul_le_mul_of_nonneg_left htan hKpos.le
    have h2 : 66218479 / 10 ^ 8 * (1 - β * ((1 - z2) - u0)) ≤ K * (1 - β * ((1 - z2) - u0)) :=
      mul_le_mul_of_nonneg_right hKlo hpos1.le
    have h3 : (1 - z2) * (1 - 41065576 / 10 ^ 8) ≤ (1 - z2) * (1 - a) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    rw [hβ, hu0] at h1 h2
    rw [hβ]
    linarith
  have hc : (5893 / 10000 : ℝ) < 1 - a := by linarith
  -- the two endpoint expressions
  obtain ⟨T0, hT0def⟩ : ∃ T, T = (g2 - a) / β + (1 - E) + (1 - z2) * (E - a) / β := ⟨_, rfl⟩
  obtain ⟨Tz, hTzdef⟩ : ∃ T, T = (1 - E) * (1 - z2) + (1 - z2) * (E - a) / β + z2 * (1 - a) := ⟨_, rfl⟩
  have hβpos : 0 < β := by rw [hβ]; norm_num
  have hT0 : (5893 / 10000 : ℝ) < T0 := by
    have hA : (5893 / 10000 : ℝ) < (g2 - a) / β + 1 - a := by
      have : 0 ≤ (g2 - a) / β := div_nonneg (by linarith) hβpos.le
      linarith
    have hB : (5893 / 10000 : ℝ) < (g2 - a) / β + (1 - z2) * (1 - a) / β := by
      rw [← add_div, lt_div_iff₀ hβpos]; linarith
    have hid : (1 - a) * T0 = (1 - E) * ((g2 - a) / β + 1 - a)
        + (E - a) * ((g2 - a) / β + (1 - z2) * (1 - a) / β) := by
      rw [hT0def]; field_simp <;> ring
    obtain ⟨m, hm⟩ : ∃ m, m = min ((g2 - a) / β + 1 - a) ((g2 - a) / β + (1 - z2) * (1 - a) / β) :=
      ⟨_, rfl⟩
    have hm1 : m ≤ (g2 - a) / β + 1 - a := by rw [hm]; exact min_le_left _ _
    have hm2 : m ≤ (g2 - a) / β + (1 - z2) * (1 - a) / β := by rw [hm]; exact min_le_right _ _
    have hmc : 5893 / 10000 < m := by rw [hm]; exact lt_min hA hB
    have e1 := mul_le_mul_of_nonneg_left hm1 (by linarith : (0 : ℝ) ≤ 1 - E)
    have e2 := mul_le_mul_of_nonneg_left hm2 (by linarith : (0 : ℝ) ≤ E - a)
    have : (1 - a) * m ≤ (1 - a) * T0 := by rw [hid]; nlinarith
    have h1a : 0 < 1 - a := by linarith
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hTz' : (5893 / 10000 : ℝ) < Tz := by
    have hB : 1 - a ≤ (1 - z2) * (1 - a) / β + z2 * (1 - a) := by
      have h1 : (1 - z2) * (1 - a) ≤ (1 - z2) * (1 - a) / β := by
        rw [le_div_iff₀ hβpos]
        have : 0 ≤ (1 - z2) * (1 - a) := mul_nonneg (by linarith) (by linarith)
        rw [hβ]; nlinarith
      nlinarith
    have hid : (1 - a) * Tz = (1 - E) * (1 - a)
        + (E - a) * ((1 - z2) * (1 - a) / β + z2 * (1 - a)) := by
      rw [hTzdef]; field_simp <;> ring
    have e1 := mul_le_mul_of_nonneg_left hB (by linarith : (0 : ℝ) ≤ E - a)
    have h1a : 0 < 1 - a := by linarith
    have : (1 - a) * (1 - a) ≤ (1 - a) * Tz := by rw [hid]; nlinarith
    have : 1 - a ≤ Tz := le_of_mul_le_mul_left this h1a
    linarith
  -- chord inequality from convexity
  have hchord : z2 * g1 ≤ (z2 - z1) * a + z1 * g2 := by
    rcases eq_or_lt_of_le (le_trans hz1 hz12) with h0 | h0
    · have hz1' : z1 = 0 := by linarith
      rw [← h0, hz1']; simp
    · set l := z1 / z2 with hl
      have hl0 : 0 ≤ l := div_nonneg hz1 h0.le
      have hl1 : l ≤ 1 := (div_le_one h0).2 hz12
      have hconv := convexOn_exp.2 (Set.mem_univ (β * (0 - 1))) (Set.mem_univ (β * (z2 - 1)))
        (by linarith : (0 : ℝ) ≤ 1 - l) hl0 (by ring)
      simp only [smul_eq_mul] at hconv
      have harg : (1 - l) * (β * (0 - 1)) + l * (β * (z2 - 1)) = β * (z1 - 1) := by
        have : l * z2 = z1 := by rw [hl]; field_simp
        linear_combination β * this
      rw [harg] at hconv
      have hg1' : g1 = Real.exp (β * (z1 - 1)) := by rw [hg1]; rfl
      have ha'' : a = Real.exp (β * (0 - 1)) := by rw [ha]; rfl
      have hg2' : g2 = Real.exp (β * (z2 - 1)) := by rw [hg2]; rfl
      rw [hg1', ha'', hg2']
      have := mul_le_mul_of_nonneg_left hconv h0.le
      have e : z2 * ((1 - l) * Real.exp (β * (0 - 1)) + l * Real.exp (β * (z2 - 1)))
          = (z2 - z1) * Real.exp (β * (0 - 1)) + z1 * Real.exp (β * (z2 - 1)) := by
        have : l * z2 = z1 := by rw [hl]; field_simp
        linear_combination (Real.exp (β * (z2 - 1)) - Real.exp (β * (0 - 1))) * this
      linarith
  -- combine
  have hf : z2 * (g2 / β - g1 / β + (1 - E) * (1 - z1) + (1 - z2) * (E / β - a / β) + z1 * (1 - a))
      - ((z2 - z1) * T0 + z1 * Tz) = (z2 * (g2 - g1) - (z2 - z1) * (g2 - a)) / β := by
    rw [hT0def, hTzdef]; field_simp <;> ring
  have hchord' : 0 ≤ (z2 * (g2 - g1) - (z2 - z1) * (g2 - a)) / β :=
    div_nonneg (by nlinarith) hβpos.le
  rcases eq_or_lt_of_le (le_trans hz1 hz12) with h0 | h0
  · have hz1' : z1 = 0 := by linarith
    have hz2' : z2 = 0 := h0.symm
    have hz12' : z1 = z2 := by linarith
    have hg12 : g1 = g2 := by rw [hg1, hg2, hz12']
    rw [hz1', hg12]
    have : T0 = g2 / β - g2 / β + (1 - E) * (1 - 0) + (1 - z2) * (E / β - a / β) + 0 * (1 - a) := by
      rw [hT0def, hz2', ← hg12, hg1, hz1', ← ha]; ring
    linarith
  · obtain ⟨m, hm⟩ : ∃ m, m = min (T0 - 5893 / 10000) (Tz - 5893 / 10000) := ⟨_, rfl⟩
    have hmpos : 0 < m := by
      rw [hm]; exact lt_min (sub_pos.2 hT0) (sub_pos.2 hTz')
    have e1 : (z2 - z1) * m ≤ (z2 - z1) * (T0 - 5893 / 10000) :=
      mul_le_mul_of_nonneg_left (by rw [hm]; exact min_le_left _ _) (sub_nonneg.2 hz12)
    have e2 : z1 * m ≤ z1 * (Tz - 5893 / 10000) :=
      mul_le_mul_of_nonneg_left (by rw [hm]; exact min_le_right _ _) hz1
    by_contra hcon
    push_neg at hcon
    have h3 := mul_le_mul_of_nonneg_left hcon h0.le
    have hzm := mul_pos h0 hmpos
    have x1 : (z2 - z1) * m = z2 * m - z1 * m := by ring
    have x2 : (z2 - z1) * (T0 - 5893 / 10000) = z2 * T0 - z1 * T0 - 5893 / 10000 * z2
        + 5893 / 10000 * z1 := by ring
    have x3 : z1 * (Tz - 5893 / 10000) = z1 * Tz - 5893 / 10000 * z1 := by ring
    have x4 : (z2 - z1) * T0 + z1 * Tz = z2 * T0 - z1 * T0 + z1 * Tz := by ring
    rw [x1, x2] at e1
    rw [x3] at e2
    rw [x4] at hf
    linarith only [e1, e2, h3, hzm, hf, hchord']
