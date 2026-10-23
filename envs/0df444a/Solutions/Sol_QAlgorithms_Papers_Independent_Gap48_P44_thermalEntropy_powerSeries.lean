-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P44.thermalEntropy_powerSeries
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:02:15.889211+00:00
-- url     : https://prove2.me/submissions/35aabffe-2ddf-43f3-8dc9-c153b2537b8c

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P44
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P44

open Filter

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)


theorem g78m_log {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun j : ℕ => (-1) ^ j * x ^ (j + 1) / ((j : ℝ) + 1)) (Real.log (1 + x)) := by
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one (x := -x) (by rw [abs_neg, abs_of_nonneg hx0]; exact hx1)).neg
  rw [sub_neg_eq_add, neg_neg] at h
  have e : (fun j : ℕ => (-1) ^ j * x ^ (j + 1) / ((j : ℝ) + 1)) =
      fun n : ℕ => -((-x) ^ (n + 1) / ((n : ℝ) + 1)) := by
    funext j; rw [neg_pow x (j + 1), pow_succ (-1 : ℝ) j]; ring
  rw [e]; exact h

theorem g78m_two {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasSum (fun j : ℕ => (-1) ^ j * x ^ (j + 1) / ((j : ℝ) + 2)) (1 - Real.log (1 + x) / x) := by
  have h := (hasSum_nat_add_iff' 1).2 (g78m_log hx0.le hx1)
  have h2 := h.mul_left (-1 / x)
  have e1 : (fun j : ℕ => (-1) ^ j * x ^ (j + 1) / ((j : ℝ) + 2)) =
      fun i : ℕ => -1 / x * ((-1) ^ (i + 1) * x ^ (i + 1 + 1) / (((i + 1 : ℕ) : ℝ) + 1)) := by
    funext j
    push_cast
    rw [pow_succ (-1 : ℝ) j, pow_succ x (j + 1)]
    field_simp
    ring
  have e2 : 1 - Real.log (1 + x) / x = -1 / x * (Real.log (1 + x) -
      ∑ i ∈ Finset.range 1, (-1) ^ i * x ^ (i + 1) / ((i : ℝ) + 1)) := by
    simp only [Finset.sum_range_one, pow_zero, one_mul, zero_add, Nat.cast_zero, pow_one, div_one]
    field_simp
    ring
  rw [e1, e2]; exact h2

theorem g78m_main {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasSum (fun j : ℕ => (-1) ^ j * x ^ (j + 1) / (((j : ℝ) + 1) * ((j : ℝ) + 2)))
      (Real.log (1 + x) - 1 + Real.log (1 + x) / x) := by
  have h := (g78m_log hx0.le hx1).sub (g78m_two hx0 hx1)
  have e : (fun j : ℕ => (-1) ^ j * x ^ (j + 1) / (((j : ℝ) + 1) * ((j : ℝ) + 2))) =
      fun j : ℕ => (-1) ^ j * x ^ (j + 1) / ((j : ℝ) + 1) - (-1) ^ j * x ^ (j + 1) / ((j : ℝ) + 2) := by
    funext j
    have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (j : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [e, show Real.log (1 + x) - 1 + Real.log (1 + x) / x =
    Real.log (1 + x) - (1 - Real.log (1 + x) / x) by ring]
  exact h

theorem g78m_bound (j : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖(-1) ^ j * x ^ (j + 1) / (((j : ℝ) + 1) * ((j : ℝ) + 2))‖ ≤ 1 / (((j : ℝ) + 1) ^ 2) := by
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_pow, abs_of_nonneg hx.1, abs_of_pos (by positivity)]
  have hp : x ^ (j + 1) ≤ 1 := pow_le_one₀ hx.1 hx.2
  have hp0 : 0 ≤ x ^ (j + 1) := pow_nonneg hx.1 _
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem g78m_all {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    HasSum (fun j : ℕ => (-1) ^ j * x ^ (j + 1) / (((j : ℝ) + 1) * ((j : ℝ) + 2)))
      (Real.log (1 + x) - 1 + Real.log (1 + x) / x) := by
  rcases hx1.lt_or_eq with h | h
  · exact g78m_main hx0 h
  · subst h
    have hsum : Summable (fun j : ℕ => 1 / (((j : ℝ) + 1) ^ 2)) := by
      have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
      simpa using this
    set F : ℝ → ℝ := fun x => ∑' j : ℕ, (-1) ^ j * x ^ (j + 1) / (((j : ℝ) + 1) * ((j : ℝ) + 2))
    have hc : ContinuousOn F (Set.Icc 0 1) :=
      continuousOn_tsum (fun j => by fun_prop) hsum fun j x hx => g78m_bound j hx
    have hs1 : Summable (fun j : ℕ => (-1) ^ j * (1 : ℝ) ^ (j + 1) / (((j : ℝ) + 1) * ((j : ℝ) + 2))) :=
      Summable.of_norm_bounded hsum fun j => g78m_bound j ⟨zero_le_one, le_rfl⟩
    have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) := Ioo_mem_nhdsLT (by norm_num)
    have hF : Filter.Tendsto F (nhdsWithin 1 (Set.Iio 1)) (nhds (F 1)) :=
      ((hc 1 ⟨zero_le_one, le_rfl⟩).mono Set.Ioo_subset_Icc_self).tendsto.mono_left
        (nhdsWithin_le_of_mem hmem)
    set H : ℝ → ℝ := fun x => Real.log (1 + x) - 1 + Real.log (1 + x) / x
    have hH : ContinuousAt H 1 := by
      have h1 : ContinuousAt (fun x : ℝ => Real.log (1 + x)) 1 :=
        (continuousAt_const.add continuousAt_id).log (by norm_num)
      exact (h1.sub continuousAt_const).add (h1.div continuousAt_id (by norm_num))
    have heq : F =ᶠ[nhdsWithin 1 (Set.Iio 1)] H := by
      filter_upwards [hmem] with y hy
      exact (g78m_main hy.1 hy.2).tsum_eq
    have hlim : Filter.Tendsto F (nhdsWithin 1 (Set.Iio 1)) (nhds (H 1)) :=
      (hH.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm
    have := tendsto_nhds_unique hF hlim
    have h1 := hs1.hasSum
    rw [show (∑' j : ℕ, (-1) ^ j * (1 : ℝ) ^ (j + 1) / (((j : ℝ) + 1) * ((j : ℝ) + 2))) = F 1 from rfl,
      this] at h1
    exact h1

/-- PDF p.7, Lemma 4: convergent power series in NATS, including N=1.
The natural index j starts at zero here, so the printed series index is j+1. -/
theorem solution (N : ℝ) (hN : 1 ≤ N) :
    HasSum (fun j : ℕ =>
      (-1 : ℝ) ^ (j + 2) /
        (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ) * N ^ (j + 1)))
      (g N - Real.log N - 1) := by
  have hN0 : 0 < N := by linarith
  have hNne : N ≠ 0 := hN0.ne'
  have h := g78m_all (x := 1 / N) (by positivity) (by rw [div_le_one hN0]; exact hN)
  have e : (fun j : ℕ => (-1 : ℝ) ^ (j + 2) /
      (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ) * N ^ (j + 1))) =
      fun j : ℕ => (-1) ^ j * (1 / N) ^ (j + 1) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
    funext j
    push_cast
    rw [pow_add (-1 : ℝ) j 2, div_pow, one_pow]
    field_simp
  have hv : g N - Real.log N - 1 =
      Real.log (1 + 1 / N) - 1 + Real.log (1 + 1 / N) / (1 / N) := by
    have h1 : (1 : ℝ) + 1 / N = (N + 1) / N := by field_simp
    rw [h1, Real.log_div (by positivity) hN0.ne']
    simp only [g]
    field_simp
    ring
  rw [e, hv]; exact h



end
