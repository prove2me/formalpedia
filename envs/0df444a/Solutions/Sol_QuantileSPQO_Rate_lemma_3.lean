-- Prove2me | solution 1 for QuantileSPQO.Rate.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T19:59:14.534772+00:00
-- url     : https://prove2.me/submissions/5b7662e8-5aa9-418f-af35-78c913371005

import Mathlib

open Filter Topology

theorem solution (a p s : ℝ) (ha : 0 < a) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (w : ℕ → ℝ) (hw_pos : ∀ i : ℕ, 1 ≤ i → 0 < w i)
    (hw : ∃ C : ℝ, ∀ᶠ i : ℕ in atTop, w i ≤ C / (i : ℝ) ^ s) :
    ∃ C' : ℝ, ∀ᶠ k : ℕ in atTop,
      ∑ i ∈ Finset.Icc 1 k, (∏ j ∈ Finset.Ioc i k, (1 - a / (j : ℝ) ^ p)) * (a / (i : ℝ) ^ p) * w i
        ≤ C' * (k : ℝ) ^ (-s) := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨C0, hC0⟩ := hw
  set C := max C0 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  set u : ℕ → ℝ := fun j => a / (j : ℝ) ^ p with hudef
  set S : ℕ → ℝ := fun k =>
    ∑ i ∈ Finset.Icc 1 k, (∏ j ∈ Finset.Ioc i k, (1 - u j)) * u i * w i with hSdef
  have hrec : ∀ k : ℕ, S (k + 1) = (1 - u (k + 1)) * S k + u (k + 1) * w (k + 1) := by
    intro k
    simp only [hSdef]
    rw [Finset.sum_Icc_succ_top (by omega), Finset.mul_sum]
    simp only [Finset.Ioc_self, Finset.prod_empty, one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [Finset.prod_Ioc_succ_top (by omega)]
    ring
  have hw' : ∀ᶠ i : ℕ in atTop, w i ≤ C * (i : ℝ) ^ (-s) := by
    filter_upwards [hC0, eventually_ge_atTop 1] with i hi hi1
    have hi0 : (0 : ℝ) < i := by exact_mod_cast hi1
    have : 0 < (i : ℝ) ^ s := Real.rpow_pos_of_pos hi0 s
    rw [Real.rpow_neg hi0.le, ← div_eq_mul_inv]
    exact hi.trans (div_le_div_of_nonneg_right (le_max_left _ _) this.le)
  have hpow : Tendsto (fun k : ℕ => (k : ℝ) ^ p) atTop atTop :=
    (tendsto_rpow_atTop hp0).comp tendsto_natCast_atTop_atTop
  have hu1 : ∀ᶠ k : ℕ in atTop, u k ≤ 1 := by
    filter_upwards [hpow.eventually_ge_atTop a, eventually_ge_atTop 1] with k hk hk1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have : 0 < (k : ℝ) ^ p := Real.rpow_pos_of_pos hk0 p
    simp only [hudef]
    rw [div_le_one this]; exact hk
  have hneg : Tendsto (fun k : ℕ => (k : ℝ) ^ (p - 1)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < 1 - p)).comp
      tendsto_natCast_atTop_atTop
    refine h.congr (fun k => ?_)
    simp [Function.comp, neg_sub]
  have hkey : ∀ᶠ k : ℕ in atTop, 2 * s * (k : ℝ) ^ p ≤ a * ((k : ℝ) - 1) := by
    have hpos : (0 : ℝ) < a / (4 * s) := by positivity
    filter_upwards [hneg.eventually (ge_mem_nhds hpos), eventually_ge_atTop 2] with k hk hk2
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    have hsplit : (k : ℝ) ^ p = (k : ℝ) ^ (p - 1) * k := by
      rw [← Real.rpow_add_one hk0.ne']; ring_nf
    rw [hsplit]
    have h1 : 2 * s * (k : ℝ) ^ (p - 1) ≤ a / 2 := by
      have := mul_le_mul_of_nonneg_left hk (by positivity : (0 : ℝ) ≤ 2 * s)
      calc 2 * s * (k : ℝ) ^ (p - 1) ≤ 2 * s * (a / (4 * s)) := this
        _ = a / 2 := by field_simp; ring
    have h2 : 0 ≤ (k : ℝ) ^ (p - 1) := (Real.rpow_pos_of_pos hk0 _).le
    nlinarith
  obtain ⟨K, hK⟩ := (hw'.and (hu1.and (hkey.and (eventually_ge_atTop 2)))).exists_forall_of_atTop
  refine ⟨max (2 * C) (S K * (K : ℝ) ^ s), ?_⟩
  filter_upwards [eventually_ge_atTop K] with k hk
  show S k ≤ _
  induction k, hk using Nat.le_induction with
  | base =>
    have hK2 := (hK K le_rfl).2.2.2
    have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    have h1 : S K = S K * (K : ℝ) ^ s * (K : ℝ) ^ (-s) := by
      rw [mul_assoc, ← Real.rpow_add hK0]; simp
    calc S K = S K * (K : ℝ) ^ s * (K : ℝ) ^ (-s) := h1
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_pos_of_pos hK0 _).le
  | succ k hk ih =>
    obtain ⟨hwk, huk, hkk, -⟩ := hK (k + 1) (by omega)
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (le_trans (hK K le_rfl).2.2.2 hk)
    have hx0 : (0 : ℝ) < k := by linarith
    set B := max (2 * C) (S K * (K : ℝ) ^ s) with hB
    have hB2 : 2 * C ≤ B := le_max_left _ _
    have hy0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    set A := ((k + 1 : ℕ) : ℝ) ^ (-s) with hA
    have hApos : 0 < A := Real.rpow_pos_of_pos hy0 _
    -- Bernoulli: (k+1)^s ≤ k^s (1 + s/k)
    have hbern : ((k + 1 : ℕ) : ℝ) ^ s ≤ (k : ℝ) ^ s * (1 + s / k) := by
      have e : ((k + 1 : ℕ) : ℝ) = (k : ℝ) * (1 + 1 / k) := by
        push_cast; field_simp
      rw [e, Real.mul_rpow hx0.le (by positivity)]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos hx0 _).le
      have := rpow_one_add_le_one_add_mul_self (by
        have : (0 : ℝ) ≤ 1 / k := by positivity
        linarith : (-1 : ℝ) ≤ 1 / k) hs0.le hs1.le
      calc (1 + 1 / (k : ℝ)) ^ s ≤ 1 + s * (1 / k) := this
        _ = 1 + s / k := by ring
    have hXs : (k : ℝ) ^ (-s) ≤ A * (1 + s / k) := by
      rw [hA, Real.rpow_neg hx0.le, Real.rpow_neg hy0.le]
      have h1 : 0 < (k : ℝ) ^ s := Real.rpow_pos_of_pos hx0 _
      have h2 : 0 < ((k + 1 : ℕ) : ℝ) ^ s := Real.rpow_pos_of_pos hy0 _
      rw [inv_le_iff_one_le_mul₀ h1]
      calc (1 : ℝ) = ((k + 1 : ℕ) : ℝ) ^ s * (((k + 1 : ℕ) : ℝ) ^ s)⁻¹ := by
            field_simp
        _ ≤ ((k : ℝ) ^ s * (1 + s / k)) * (((k + 1 : ℕ) : ℝ) ^ s)⁻¹ :=
            mul_le_mul_of_nonneg_right hbern (inv_nonneg.mpr h2.le)
        _ = _ := by ring
    have hu0 : 0 ≤ u (k + 1) := by
      simp only [hudef]; exact div_nonneg ha.le (Real.rpow_pos_of_pos hy0 _).le
    have hsx : s / k ≤ u (k + 1) / 2 := by
      have hyp : 0 < ((k + 1 : ℕ) : ℝ) ^ p := Real.rpow_pos_of_pos hy0 _
      simp only [hudef]
      rw [div_le_iff₀ hx0, div_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : ((k + 1 : ℕ) : ℝ) - 1 = k := by push_cast; ring
      rw [this] at hkk
      nlinarith
    have hwk' : w (k + 1) ≤ C * A := hwk
    rw [hrec]
    have h1u : 0 ≤ 1 - u (k + 1) := by linarith
    have hB0 : 0 ≤ B := by linarith
    calc (1 - u (k + 1)) * S k + u (k + 1) * w (k + 1)
        ≤ (1 - u (k + 1)) * (B * (k : ℝ) ^ (-s)) + u (k + 1) * (C * A) := by
          gcongr
      _ ≤ (1 - u (k + 1)) * (B * (A * (1 + u (k + 1) / 2))) + u (k + 1) * (B / 2 * A) := by
          gcongr
          · calc (k : ℝ) ^ (-s) ≤ A * (1 + s / k) := hXs
              _ ≤ A * (1 + u (k + 1) / 2) := by gcongr
          · linarith
      _ ≤ B * A := by nlinarith [mul_nonneg hB0 hApos.le, mul_nonneg (mul_nonneg hB0 hApos.le) (mul_nonneg hu0 hu0)]
