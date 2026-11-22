-- Prove2me | solution 1 for VehShare.MultiNet.multi_network_bound
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T07:28:55.604342+00:00
-- url     : https://prove2.me/submissions/3518b5d4-7d16-4558-bf12-f6b34c940e1f

import Mathlib

set_option maxHeartbeats 4000000

/-- The first AM-GM consequence used in the rounding core. -/
private lemma key_D1 {a₁ a₂ k m : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    0 ≤ a₂ * k * (k + 1) * (a₂ + 1) + a₁ * m * (m - 1) * (a₁ + 1)
      - 2 * (a₁ * a₂ * k * (m - 1)) := by
  have hX : 0 ≤ a₂ * k * (k + 1) * (a₂ + 1) := by
    apply mul_nonneg (mul_nonneg (mul_nonneg ha₂ (by linarith)) (by linarith))
    linarith
  have hY : 0 ≤ a₁ * m * (m - 1) * (a₁ + 1) := by
    apply mul_nonneg (mul_nonneg (mul_nonneg ha₁ (by linarith)) (by linarith))
    linarith
  have hZ : 0 ≤ a₁ * a₂ * k * (m - 1) := by
    apply mul_nonneg (mul_nonneg (mul_nonneg ha₁ ha₂) (by linarith))
    linarith
  have hkey : a₁ * a₂ * k * (m - 1) ≤ (k + 1) * m * (a₂ + 1) * (a₁ + 1) := by
    have hc : (0:ℝ) ≤ a₁ * a₂ * k := by positivity
    have h1 : a₁ * a₂ * k * (m - 1) ≤ a₁ * a₂ * k * m :=
      mul_le_mul_of_nonneg_left (by linarith : m - 1 ≤ m) hc
    have h4 : a₁ * a₂ ≤ (a₁ + 1) * (a₂ + 1) := by nlinarith
    have h5 : a₁ * a₂ * k ≤ ((a₁ + 1) * (a₂ + 1)) * (k + 1) :=
      mul_le_mul h4 (by linarith) (by linarith) (by positivity)
    have h6 : a₁ * a₂ * k * m ≤ (k + 1) * m * (a₂ + 1) * (a₁ + 1) := by
      have := mul_le_mul_of_nonneg_right h5 (by linarith : (0:ℝ) ≤ m)
      nlinarith [this]
    linarith
  have hprod : (a₁ * a₂ * k * (m - 1)) ^ 2
      ≤ (a₂ * k * (k + 1) * (a₂ + 1)) * (a₁ * m * (m - 1) * (a₁ + 1)) := by
    have h := mul_le_mul_of_nonneg_left hkey hZ
    nlinarith [h]
  have h1 : a₁ * a₂ * k * (m - 1)
      ≤ Real.sqrt ((a₂ * k * (k + 1) * (a₂ + 1)) * (a₁ * m * (m - 1) * (a₁ + 1))) := by
    rw [← Real.sqrt_sq hZ]
    exact Real.sqrt_le_sqrt hprod
  have h2 : 2 * Real.sqrt ((a₂ * k * (k + 1) * (a₂ + 1)) * (a₁ * m * (m - 1) * (a₁ + 1)))
      ≤ (a₂ * k * (k + 1) * (a₂ + 1)) + (a₁ * m * (m - 1) * (a₁ + 1)) := by
    have h := two_mul_le_add_sq (Real.sqrt (a₂ * k * (k + 1) * (a₂ + 1)))
      (Real.sqrt (a₁ * m * (m - 1) * (a₁ + 1)))
    rw [Real.sq_sqrt hX, Real.sq_sqrt hY] at h
    have hmul : Real.sqrt ((a₂ * k * (k + 1) * (a₂ + 1)) * (a₁ * m * (m - 1) * (a₁ + 1)))
        = Real.sqrt (a₂ * k * (k + 1) * (a₂ + 1)) * Real.sqrt (a₁ * m * (m - 1) * (a₁ + 1)) :=
      Real.sqrt_mul hX _
    linarith [h, hmul]
  linarith

/-- The second AM-GM consequence used in the rounding core. -/
private lemma key_D2 {a₁ a₂ k m : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    0 ≤ a₂ * k * (k - 1) * (a₂ + 1) + a₁ * m * (m + 1) * (a₁ + 1)
      - 2 * (a₁ * a₂ * m * (k - 1)) := by
  have hX : 0 ≤ a₂ * k * (k - 1) * (a₂ + 1) := by
    apply mul_nonneg (mul_nonneg (mul_nonneg ha₂ (by linarith)) (by linarith))
    linarith
  have hY : 0 ≤ a₁ * m * (m + 1) * (a₁ + 1) := by
    apply mul_nonneg (mul_nonneg (mul_nonneg ha₁ (by linarith)) (by linarith))
    linarith
  have hZ : 0 ≤ a₁ * a₂ * m * (k - 1) := by
    apply mul_nonneg (mul_nonneg (mul_nonneg ha₁ ha₂) (by linarith))
    linarith
  have hkey : a₁ * a₂ * m * (k - 1) ≤ k * (m + 1) * (a₂ + 1) * (a₁ + 1) := by
    have hc : (0:ℝ) ≤ a₁ * a₂ * m := by positivity
    have h1 : a₁ * a₂ * m * (k - 1) ≤ a₁ * a₂ * m * k :=
      mul_le_mul_of_nonneg_left (by linarith : k - 1 ≤ k) hc
    have h4 : a₁ * a₂ ≤ (a₁ + 1) * (a₂ + 1) := by nlinarith
    have h5 : a₁ * a₂ * m ≤ ((a₁ + 1) * (a₂ + 1)) * (m + 1) :=
      mul_le_mul h4 (by linarith) (by linarith) (by positivity)
    have h6 : a₁ * a₂ * m * k ≤ k * (m + 1) * (a₂ + 1) * (a₁ + 1) := by
      have := mul_le_mul_of_nonneg_right h5 (by linarith : (0:ℝ) ≤ k)
      nlinarith [this]
    linarith
  have hprod : (a₁ * a₂ * m * (k - 1)) ^ 2
      ≤ (a₂ * k * (k - 1) * (a₂ + 1)) * (a₁ * m * (m + 1) * (a₁ + 1)) := by
    have h := mul_le_mul_of_nonneg_left hkey hZ
    nlinarith [h]
  have h1 : a₁ * a₂ * m * (k - 1)
      ≤ Real.sqrt ((a₂ * k * (k - 1) * (a₂ + 1)) * (a₁ * m * (m + 1) * (a₁ + 1))) := by
    rw [← Real.sqrt_sq hZ]
    exact Real.sqrt_le_sqrt hprod
  have h2 : 2 * Real.sqrt ((a₂ * k * (k - 1) * (a₂ + 1)) * (a₁ * m * (m + 1) * (a₁ + 1)))
      ≤ (a₂ * k * (k - 1) * (a₂ + 1)) + (a₁ * m * (m + 1) * (a₁ + 1)) := by
    have h := two_mul_le_add_sq (Real.sqrt (a₂ * k * (k - 1) * (a₂ + 1)))
      (Real.sqrt (a₁ * m * (m + 1) * (a₁ + 1)))
    rw [Real.sq_sqrt hX, Real.sq_sqrt hY] at h
    have hmul : Real.sqrt ((a₂ * k * (k - 1) * (a₂ + 1)) * (a₁ * m * (m + 1) * (a₁ + 1)))
        = Real.sqrt (a₂ * k * (k - 1) * (a₂ + 1)) * Real.sqrt (a₁ * m * (m + 1) * (a₁ + 1)) :=
      Real.sqrt_mul hX _
    linarith [h, hmul]
  linarith

/-- The rational rearrangement used at the end of the two-network argument. -/
private lemma hdiff_rearrange (w₁ w₂ a₁ a₂ u v K : ℝ)
    (hK : u + v = a₁ + a₂ + K) (hu : 0 < u) (hv : 0 < v) :
    (w₁ + w₂) * (a₁ + a₂ + 1) / (u + v + 1) - (w₁ * a₁ / u + w₂ * a₂ / v)
      = (w₁ * v * ((a₁ + a₂ + 1) * (u - a₁) - a₁ * K)
          + w₂ * u * ((a₁ + a₂ + 1) * (v - a₂) - a₂ * K)) / (u * v * (u + v + 1)) := by
  have hK' : K = u + v - a₁ - a₂ := by linarith
  rw [hK']
  have h1 : u + v + 1 ≠ 0 := by linarith
  field_simp [hu.ne', hv.ne', h1]
  ring

/-- The step identity, increasing branch. -/
private lemma step_frac_up (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) :
    (x + 1) / (a + (x + 1)) - x / (a + x) = a / ((a + x) * (a + x + 1)) := by
  have h1 : 0 < a + x := by linarith
  have h2 : 0 < a + x + 1 := by linarith
  have e : a + (x + 1) = a + x + 1 := by ring
  rw [e]
  field_simp (disch := positivity)
  ring

/-- The step identity, decreasing branch. -/
private lemma step_frac_down (a x : ℝ) (ha : 0 < a) (hx : 1 ≤ x) :
    x / (a + x) - (x - 1) / (a + (x - 1)) = a / ((a + x) * (a + x - 1)) := by
  have h1 : 0 < a + x := by linarith
  have h2 : 0 < a + x - 1 := by linarith
  have e : a + (x - 1) = a + x - 1 := by ring
  rw [e]
  field_simp (disch := positivity)
  ring

/-- Rewriting a multiple of x / (a + x). -/
private lemma mul_div_add (W a x : ℝ) (h : a + x ≠ 0) :
    W * x / (a + x) = W - W * a / (a + x) := by
  field_simp [h]
  ring

/-- Degenerate case: one of the two atoms is empty. -/
private lemma degenerate_zero (W₁ W₂ a K : ℝ) (hW₁ : 0 ≤ W₁) (hW₂ : 0 ≤ W₂)
    (ha : 0 < a) (hK : 1 ≤ K) :
    (W₁ + W₂) * K / (a + K + 1) ≤ W₂ * K / (a + K) ∨
      (W₁ + W₂) * K / (a + K + 1) ≤ W₁ + W₂ * (K - 1) / (a + (K - 1)) := by
  rcases le_or_gt (W₁ * (a + K)) W₂ with hcase | hcase
  · left
    have hK0 : 0 ≤ K := by linarith
    rw [div_le_iff₀ (by linarith : (0:ℝ) < a + K + 1)]
    rw [div_mul_eq_mul_div]
    rw [le_div_iff₀ (by linarith : (0:ℝ) < a + K)]
    nlinarith [mul_le_mul_of_nonneg_right hcase hK0]
  · right
    have hd1 : (0:ℝ) < a + K + 1 := by linarith
    have hd2 : (0:ℝ) < a + (K - 1) := by linarith
    rw [div_le_iff₀ hd1]
    have hdist : (W₁ + W₂ * (K - 1) / (a + (K - 1))) * (a + K + 1)
        = W₁ * (a + K + 1) + W₂ * (K - 1) / (a + (K - 1)) * (a + K + 1) := by ring
    have hX : W₂ * (K - 1) / (a + (K - 1)) * (a + K + 1)
        = W₂ * (K - 1) * (a + K + 1) / (a + (K - 1)) := by
      rw [div_mul_eq_mul_div]
    rw [hdist, hX, add_comm (W₁ * (a + K + 1)), ← sub_le_iff_le_add]
    rw [le_div_iff₀ hd2]
    rcases le_or_gt 0 (K - a - 1) with hc | hc
    · nlinarith [hW₁, hW₂, hc]
    · have hlt := mul_lt_mul_of_neg_right hcase hc
      have hDA : 0 ≤ W₁ * (1 + a) * (a + (K - 1)) + W₁ * (a + K) * (K - a - 1) := by
        have heq : W₁ * (1 + a) * (a + (K - 1)) + W₁ * (a + K) * (K - a - 1)
            = W₁ * (K - 1) * (a + K + 1) := by ring
        rw [heq]
        have hK0 : 0 ≤ K - 1 := by linarith
        have hA0 : 0 ≤ a + K + 1 := by linarith
        positivity
      nlinarith [hlt, hDA]

/-- The case `B₂ < 0` of the final sign split, isolated to keep the context small. -/
private lemma hG_case_neg {w₁ w₂ a₁ a₂ u v B₁ B₂ : ℝ}
    (hB1 : 0 < B₁) (hD : 0 ≤ a₂ * (u - 1) * B₁ + a₁ * (v + 1) * B₂)
    (hH2 : w₂ * a₂ * (u * (u - 1)) ≤ w₁ * a₁ * (v * (v + 1)))
    (hw₂ : 0 ≤ w₂) (hu : 0 < u) (ha₁ : 0 < a₁) (hv1 : 0 < v + 1) :
    0 ≤ w₁ * v * B₁ + w₂ * u * B₂ := by
  have hD' : 0 ≤ w₂ * u * (a₂ * (u - 1) * B₁ + a₁ * (v + 1) * B₂) :=
    mul_nonneg (by positivity) hD
  have hH2B : w₂ * a₂ * (u * (u - 1)) * B₁ ≤ w₁ * a₁ * (v * (v + 1)) * B₁ :=
    mul_le_mul_of_nonneg_right hH2 hB1.le
  have hgoal : 0 ≤ a₁ * (v + 1) * (w₁ * v * B₁ + w₂ * u * B₂) := by
    nlinarith [hD', hH2B]
  exact nonneg_of_mul_nonneg_right hgoal (by positivity)

/-- The two-network rounding bound. -/
private theorem two_network_aux (w₁ w₂ : ℝ) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (N₁ N₂ : ℕ)
    (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂) (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (K : ℕ) :
    ∃ K₁ : ℕ, K₁ ≤ K ∧
      (w₁ + w₂) * K / ((N₁ : ℝ) + N₂ + K - 1 + (M₁ + M₂)) ≤
        w₁ * K₁ / ((N₁ : ℝ) + K₁ - 1 + M₁) +
          w₂ * ((K : ℝ) - K₁) / ((N₂ : ℝ) + ((K : ℝ) - K₁) - 1 + M₂) := by
  classical
  set a₁ : ℝ := (N₁ : ℝ) - 1 + M₁ with ha₁def
  set a₂ : ℝ := (N₂ : ℝ) - 1 + M₂ with ha₂def
  have ha₁ : 0 ≤ a₁ := by
    rw [ha₁def]
    have h1 : (1:ℝ) ≤ (N₁:ℝ) := by exact_mod_cast hN₁
    linarith
  have ha₂ : 0 ≤ a₂ := by
    rw [ha₂def]
    have h1 : (1:ℝ) ≤ (N₂:ℝ) := by exact_mod_cast hN₂
    linarith
  have e0 : a₁ + a₂ + (K : ℝ) + 1 = (N₁ : ℝ) + N₂ + K - 1 + (M₁ + M₂) := by
    rw [ha₁def, ha₂def]; push_cast; ring
  have e1 : ∀ k : ℕ, a₁ + (k : ℝ) = (N₁ : ℝ) + k - 1 + M₁ := by
    intro k; rw [ha₁def]; push_cast; ring
  have e2 : ∀ k : ℕ, a₂ + ((K : ℝ) - (k : ℝ)) = (N₂ : ℝ) + ((K : ℝ) - k) - 1 + M₂ := by
    intro k; rw [ha₂def]; push_cast; ring
  suffices key : ∃ K₁ : ℕ, K₁ ≤ K ∧ (w₁ + w₂) * K / (a₁ + a₂ + K + 1) ≤
      w₁ * K₁ / (a₁ + K₁) + w₂ * ((K : ℝ) - K₁) / (a₂ + ((K : ℝ) - K₁)) by
    obtain ⟨k, hkK, hk⟩ := key
    refine ⟨k, hkK, ?_⟩
    rw [← e0, ← e1 k, ← e2 k]
    exact hk
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · subst hK0
    exact ⟨0, le_refl 0, by simp⟩
  have hKpos' : (0:ℝ) < (K:ℝ) := by exact_mod_cast hKpos
  have hK1R : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hKpos
  rcases eq_or_lt_of_le ha₁ with h1 | h1
  · rcases eq_or_lt_of_le ha₂ with h2 | h2
    · -- ## a₁ = 0, a₂ = 0
      have h1z : a₁ = 0 := h1.symm
      have h2z : a₂ = 0 := h2.symm
      rcases Nat.lt_or_ge 1 K with hK2 | hK2
      · -- K ≥ 2, take K₁ = 1
        refine ⟨1, by omega, ?_⟩
        rw [h1z, h2z]
        push_cast
        have hKne : (K:ℝ) - 1 ≠ 0 := by
          have h2' : (2:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK2
          linarith
        have hR : w₁ * (1:ℝ) / ((0:ℝ) + 1) + w₂ * ((K:ℝ) - 1) / ((0:ℝ) + ((K:ℝ) - 1)) = w₁ + w₂ := by
          have hA : w₁ * (1:ℝ) / ((0:ℝ) + 1) = w₁ := by norm_num
          have hB : w₂ * ((K:ℝ) - 1) / ((0:ℝ) + ((K:ℝ) - 1)) = w₂ := by
            rw [zero_add, mul_div_assoc, div_self hKne, mul_one]
          rw [hA, hB]
        rw [hR]
        have hL : (0:ℝ) + 0 + (K:ℝ) + 1 = (K:ℝ) + 1 := by ring
        rw [hL, div_le_iff₀ (by linarith : (0:ℝ) < (K:ℝ) + 1)]
        nlinarith [hw₁, hw₂]
      · -- K = 1
        have hKeq : K = 1 := by omega
        subst hKeq
        rw [h1z, h2z]
        push_cast
        rcases le_or_gt w₁ w₂ with hw | hw
        · refine ⟨0, by omega, ?_⟩
          norm_num
          linarith
        · refine ⟨1, by omega, ?_⟩
          norm_num
          linarith
    · -- ## a₁ = 0, a₂ > 0
      have h1z : a₁ = 0 := h1.symm
      rcases degenerate_zero w₁ w₂ a₂ (K:ℝ) hw₁ hw₂ h2 hK1R with hdeg | hdeg
      · refine ⟨0, by omega, ?_⟩
        rw [h1z]
        push_cast
        simpa using hdeg
      · refine ⟨1, by omega, ?_⟩
        rw [h1z]
        push_cast
        simpa using hdeg
  · rcases eq_or_lt_of_le ha₂ with h2 | h2
    · -- ## a₁ > 0, a₂ = 0
      have h2z : a₂ = 0 := h2.symm
      rcases degenerate_zero w₂ w₁ a₁ (K:ℝ) hw₂ hw₁ h1 hK1R with hdeg | hdeg
      · refine ⟨K, le_refl K, ?_⟩
        rw [h2z]
        push_cast
        simpa [add_comm] using hdeg
      · refine ⟨K - 1, by omega, ?_⟩
        rw [h2z]
        push_cast [Nat.cast_sub hKpos]
        simpa [add_comm] using hdeg
    · -- ## a₁ > 0, a₂ > 0: the main argmax argument
      set F : ℕ → ℝ := fun k => w₁ * (k:ℝ) / (a₁ + k) + w₂ * ((K:ℝ) - k) / (a₂ + ((K:ℝ) - k)) with hF
      obtain ⟨k, hkmem, hkmax⟩ := Finset.exists_max_image (Finset.range (K+1)) F ⟨0, by simp⟩
      have hkK : k ≤ K := by
        have := Finset.mem_range.mp hkmem
        omega
      refine ⟨k, hkK, ?_⟩
      have hKR : (k:ℝ) ≤ (K:ℝ) := by exact_mod_cast hkK
      set u : ℝ := a₁ + (k:ℝ) with hu_def
      set v : ℝ := a₂ + ((K:ℝ) - k) with hv_def
      have hu : 0 < u := by rw [hu_def]; linarith
      have hv : 0 < v := by rw [hv_def]; linarith
      have hS : u + v = a₁ + a₂ + (K:ℝ) := by rw [hu_def, hv_def]; ring
      set B₁ : ℝ := (a₁ + a₂ + 1) * (u - a₁) - a₁ * (K:ℝ) with hB1_def
      set B₂ : ℝ := (a₁ + a₂ + 1) * (v - a₂) - a₂ * (K:ℝ) with hB2_def
      -- optimality inequalities from the maximality of `k`
      have hH1 : k < K → w₁ * a₁ * (v * (v - 1)) ≤ w₂ * a₂ * (u * (u + 1)) := by
        intro hklt
        rw [hu_def, hv_def]
        have hmem' : (k+1) ∈ Finset.range (K+1) := by
          simp only [Finset.mem_range]; omega
        have hle := hkmax (k+1) hmem'
        simp only [hF] at hle
        push_cast at hle
        have hk0 : (0:ℝ) ≤ (k:ℝ) := by positivity
        have hkm1 : (1:ℝ) ≤ (K:ℝ) - (k:ℝ) := by
          have h : (k:ℝ) + 1 ≤ (K:ℝ) := by exact_mod_cast (by omega : k + 1 ≤ K)
          linarith
        have hgroup : w₁ * ((k:ℝ)+1) / (a₁ + ((k:ℝ)+1)) - w₁ * (k:ℝ) / (a₁ + (k:ℝ))
            ≤ w₂ * ((K:ℝ)-(k:ℝ)) / (a₂ + ((K:ℝ)-(k:ℝ))) - w₂ * ((K:ℝ)-((k:ℝ)+1)) / (a₂ + ((K:ℝ)-((k:ℝ)+1))) := by
          linarith [hle]
        have e2 : (K:ℝ) - ((k:ℝ)+1) = ((K:ℝ) - (k:ℝ)) - 1 := by ring
        rw [e2] at hgroup
        rw [mul_div_assoc, mul_div_assoc, mul_div_assoc, mul_div_assoc] at hgroup
        rw [← mul_sub, ← mul_sub] at hgroup
        rw [step_frac_up a₁ (k:ℝ) h1 hk0, step_frac_down a₂ ((K:ℝ)-(k:ℝ)) h2 hkm1] at hgroup
        have hX : 0 < (a₁ + (k:ℝ)) * (a₁ + (k:ℝ) + 1) := by
          have hh : 0 < a₁ + (k:ℝ) := by linarith
          have hh2 : 0 < a₁ + (k:ℝ) + 1 := by linarith
          positivity
        have hY : 0 < (a₂ + ((K:ℝ) - (k:ℝ))) * (a₂ + ((K:ℝ) - (k:ℝ)) - 1) := by
          have hh : 0 < a₂ + ((K:ℝ) - (k:ℝ)) - 1 := by linarith
          have hh2 : 0 < a₂ + ((K:ℝ) - (k:ℝ)) := by linarith
          positivity
        rw [← mul_div_assoc, ← mul_div_assoc] at hgroup
        rw [div_le_iff₀ hX, div_mul_eq_mul_div, le_div_iff₀ hY] at hgroup
        exact hgroup
      have hH2 : 0 < k → w₂ * a₂ * (u * (u - 1)) ≤ w₁ * a₁ * (v * (v + 1)) := by
        intro hkpos
        rw [hu_def, hv_def]
        have hmem' : (k-1) ∈ Finset.range (K+1) := by
          simp only [Finset.mem_range]; omega
        have hle := hkmax (k-1) hmem'
        simp only [hF] at hle
        have hkc : ((k - 1 : ℕ) : ℝ) = (k:ℝ) - 1 := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
          ring
        rw [hkc] at hle
        have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hkpos
        have hm0 : (0:ℝ) ≤ (K:ℝ) - (k:ℝ) := by linarith
        have hgroup : w₂ * ((K:ℝ)-((k:ℝ)-1)) / (a₂ + ((K:ℝ)-((k:ℝ)-1))) - w₂ * ((K:ℝ)-(k:ℝ)) / (a₂ + ((K:ℝ)-(k:ℝ)))
            ≤ w₁ * (k:ℝ) / (a₁ + (k:ℝ)) - w₁ * ((k:ℝ)-1) / (a₁ + ((k:ℝ)-1)) := by
          linarith [hle]
        have e2 : (K:ℝ)-((k:ℝ)-1) = ((K:ℝ)-(k:ℝ)) + 1 := by ring
        rw [e2] at hgroup
        rw [mul_div_assoc, mul_div_assoc, mul_div_assoc, mul_div_assoc] at hgroup
        rw [← mul_sub, ← mul_sub] at hgroup
        rw [step_frac_up a₂ ((K:ℝ)-(k:ℝ)) h2 hm0, step_frac_down a₁ (k:ℝ) h1 hk1] at hgroup
        have hX : 0 < (a₁ + (k:ℝ)) * (a₁ + (k:ℝ) - 1) := by
          have hh : 0 < a₁ + (k:ℝ) - 1 := by linarith
          have hh2 : 0 < a₁ + (k:ℝ) := by linarith
          positivity
        have hY : 0 < (a₂ + ((K:ℝ)-(k:ℝ))) * (a₂ + ((K:ℝ)-(k:ℝ)) + 1) := by
          have hh : 0 < a₂ + ((K:ℝ)-(k:ℝ)) := by linarith
          have hh2 : 0 < a₂ + ((K:ℝ)-(k:ℝ)) + 1 := by linarith
          positivity
        rw [← mul_div_assoc, ← mul_div_assoc] at hgroup
        rw [div_le_iff₀ hY, div_mul_eq_mul_div, le_div_iff₀ hX] at hgroup
        exact hgroup
      -- the two endpoint inequalities
      have hD1 : 0 ≤ a₂ * (u + 1) * B₁ + a₁ * (v - 1) * B₂ := by
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · have hk0' : (k:ℝ) = 0 := by exact_mod_cast hk0
          have hu0 : u = a₁ := by rw [hu_def, hk0']; ring
          have hv0 : v = a₂ + (K:ℝ) := by rw [hv_def, hk0']; ring
          have hB1 : B₁ = -(a₁ * (K:ℝ)) := by rw [hB1_def, hu0]; ring
          have hB2 : B₂ = (a₁ + 1) * (K:ℝ) := by rw [hB2_def, hv0]; ring
          rw [hu0, hv0, hB1, hB2]
          have hgoal : 0 ≤ a₁ * (a₁ + 1) * (K:ℝ) * ((K:ℝ) - 1) := by
            have hK0 : 0 ≤ (K:ℝ) - 1 := by linarith
            positivity
          convert hgoal using 1 <;> ring
        · rcases eq_or_lt_of_le hkK with hkK' | hklt
          · have hkK'' : (k:ℝ) = (K:ℝ) := by exact_mod_cast hkK'
            have hu0 : u = a₁ + (K:ℝ) := by rw [hu_def, hkK'']
            have hv0 : v = a₂ := by rw [hv_def, hkK'']; ring
            have hB1 : B₁ = (a₂ + 1) * (K:ℝ) := by rw [hB1_def, hu0]; ring
            have hB2 : B₂ = -(a₂ * (K:ℝ)) := by rw [hB2_def, hv0]; ring
            rw [hu0, hv0, hB1, hB2]
            have hgoal : 0 ≤ a₂ * (K:ℝ) * (2 * a₁ + ((K:ℝ) + 1) * (a₂ + 1)) := by
              have hK0 : 0 ≤ (K:ℝ) := by linarith
              positivity
            convert hgoal using 1 <;> ring
          · have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hkpos
            have hm1 : (1:ℝ) ≤ (K:ℝ) - (k:ℝ) := by
              have h : (k:ℝ) + 1 ≤ (K:ℝ) := by exact_mod_cast hklt
              linarith
            rw [hB1_def, hB2_def, hu_def, hv_def]
            have hkey := key_D1 h1.le h2.le hk1 hm1
            convert hkey using 1 <;> ring
      have hD2 : 0 ≤ a₂ * (u - 1) * B₁ + a₁ * (v + 1) * B₂ := by
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · have hk0' : (k:ℝ) = 0 := by exact_mod_cast hk0
          have hu0 : u = a₁ := by rw [hu_def, hk0']; ring
          have hv0 : v = a₂ + (K:ℝ) := by rw [hv_def, hk0']; ring
          have hB1 : B₁ = -(a₁ * (K:ℝ)) := by rw [hB1_def, hu0]; ring
          have hB2 : B₂ = (a₁ + 1) * (K:ℝ) := by rw [hB2_def, hv0]; ring
          rw [hu0, hv0, hB1, hB2]
          have hgoal : 0 ≤ a₁ * (K:ℝ) * (a₁ * (K:ℝ) + a₁ + (K:ℝ) + 2 * a₂ + 1) := by
            have hK0 : 0 ≤ (K:ℝ) := by linarith
            positivity
          convert hgoal using 1 <;> ring
        · rcases eq_or_lt_of_le hkK with hkK' | hklt
          · have hkK'' : (k:ℝ) = (K:ℝ) := by exact_mod_cast hkK'
            have hu0 : u = a₁ + (K:ℝ) := by rw [hu_def, hkK'']
            have hv0 : v = a₂ := by rw [hv_def, hkK'']; ring
            have hB1 : B₁ = (a₂ + 1) * (K:ℝ) := by rw [hB1_def, hu0]; ring
            have hB2 : B₂ = -(a₂ * (K:ℝ)) := by rw [hB2_def, hv0]; ring
            rw [hu0, hv0, hB1, hB2]
            have hgoal : 0 ≤ a₂ * (K:ℝ) * (a₂ + 1) * ((K:ℝ) - 1) := by
              have hK0 : 0 ≤ (K:ℝ) - 1 := by linarith
              positivity
            convert hgoal using 1 <;> ring
          · have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hkpos
            have hm1 : (1:ℝ) ≤ (K:ℝ) - (k:ℝ) := by
              have h : (k:ℝ) + 1 ≤ (K:ℝ) := by exact_mod_cast hklt
              linarith
            rw [hB1_def, hB2_def, hu_def, hv_def]
            have hkey := key_D2 h1.le h2.le hk1 hm1
            convert hkey using 1 <;> ring
      -- combine into `G ≥ 0`
      have hBsum : B₁ + B₂ = (K:ℝ) := by
        rw [hB1_def, hB2_def, hu_def, hv_def]
        push_cast
        ring
      have hG : 0 ≤ w₁ * v * B₁ + w₂ * u * B₂ := by
        rcases le_or_gt 0 B₂ with hB2 | hB2
        · have hklt : k < K := by
            rcases lt_or_ge k K with h | h
            · exact h
            · exfalso
              have hkK' : k = K := by omega
              have hvK : v = a₂ := by
                rw [hv_def]
                rw [show (k:ℝ) = (K:ℝ) by exact_mod_cast hkK']
                ring
              have hB2' : B₂ = -(a₂ * (K:ℝ)) := by rw [hB2_def, hvK]; ring
              rw [hB2'] at hB2
              have hp : 0 < a₂ * (K:ℝ) := mul_pos h2 hKpos'
              linarith
          have hD : 0 ≤ w₁ * v * (a₂ * (u + 1) * B₁ + a₁ * (v - 1) * B₂) :=
            mul_nonneg (by positivity) hD1
          have hstep := mul_le_mul_of_nonneg_right (hH1 hklt) hB2
          have hgoal : 0 ≤ a₂ * (u + 1) * (w₁ * v * B₁ + w₂ * u * B₂) := by
            calc 0 ≤ w₁ * v * (a₂ * (u + 1) * B₁ + a₁ * (v - 1) * B₂) := hD
              _ = w₁ * v * (a₂ * (u + 1) * B₁) + w₁ * a₁ * (v * (v - 1)) * B₂ := by ring
              _ ≤ w₁ * v * (a₂ * (u + 1) * B₁) + w₂ * a₂ * (u * (u + 1)) * B₂ := by linarith
              _ = a₂ * (u + 1) * (w₁ * v * B₁ + w₂ * u * B₂) := by ring
          exact nonneg_of_mul_nonneg_right hgoal (by positivity)
        · have hkpos : 0 < k := by
            rcases Nat.eq_zero_or_pos k with h | h
            · exfalso
              have hk0' : (k:ℝ) = 0 := by exact_mod_cast h
              have hv0' : v = a₂ + (K:ℝ) := by rw [hv_def, hk0']; ring
              have hB2' : B₂ = (a₁ + 1) * (K:ℝ) := by rw [hB2_def, hv0']; ring
              rw [hB2'] at hB2
              have hp : 0 < (a₁ + 1) * (K:ℝ) := by positivity
              linarith
            · exact h
          exact hG_case_neg (by linarith) hD2 (hH2 hkpos) hw₂ hu h1 (by linarith)
      -- conclude
      have hdiff := hdiff_rearrange w₁ w₂ a₁ a₂ u v (K:ℝ) hS hu hv
      have hpos : 0 < u * v * (u + v + 1) := by positivity
      have hnn : 0 ≤ (w₁ * v * B₁ + w₂ * u * B₂) / (u * v * (u + v + 1)) :=
        div_nonneg hG hpos.le
      rw [hB1_def, hB2_def] at hnn
      have hlk : w₁ * (k:ℝ) / u = w₁ - w₁ * a₁ / u := by
        rw [hu_def]
        exact mul_div_add w₁ a₁ (k:ℝ) (by positivity)
      have hmk : w₂ * ((K:ℝ) - k) / v = w₂ - w₂ * a₂ / v := by
        rw [hv_def]
        exact mul_div_add w₂ a₂ ((K:ℝ) - (k:ℝ)) (by positivity)
      have hAK : (w₁ + w₂) * (K:ℝ) / (u + v + 1) = (w₁ + w₂) - (w₁ + w₂) * (a₁ + a₂ + 1) / (u + v + 1) := by
        rw [hS]
        have h := mul_div_add (w₁ + w₂) (a₁ + a₂ + 1) (K:ℝ) (by positivity)
        convert h using 2 <;> ring
      rw [← hS]
      rw [hlk, hmk, hAK]
      linarith [hdiff, hnn]

theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] (w : ι → ℝ)
    (hw : ∀ c, 0 ≤ w c) (n : ι → ℕ) (hn : ∀ c, 1 ≤ n c) (m : ι → ℝ) (hm : ∀ c, 0 ≤ m c)
    (K : ℕ) :
    ∃ k : ι → ℕ, ∑ c, k c = K ∧
      (∑ c, w c) * K / ((∑ c, (n c : ℝ)) + K - 1 + ∑ c, m c) ≤
        ∑ c, w c * k c / ((n c : ℝ) + k c - 1 + m c) := by
  classical
  have key : ∀ s : Finset ι, s.Nonempty → ∀ K : ℕ,
      ∃ k : ι → ℕ, (∀ c, c ∉ s → k c = 0) ∧ (∑ c ∈ s, k c) = K ∧
        (∑ c ∈ s, w c) * K / ((∑ c ∈ s, (n c : ℝ)) + K - 1 + ∑ c ∈ s, m c) ≤
          ∑ c ∈ s, w c * k c / ((n c : ℝ) + k c - 1 + m c) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro hne
        exact absurd hne (by simp)
    | insert a s' ha ih =>
        intro hne K
        by_cases hs' : s'.Nonempty
        · have hw_sum : 0 ≤ ∑ c ∈ s', w c := Finset.sum_nonneg (fun c _ => hw c)
          have hm_sum : 0 ≤ ∑ c ∈ s', m c := Finset.sum_nonneg (fun c _ => hm c)
          have hn_sum : 1 ≤ ∑ c ∈ s', n c := by
            obtain ⟨b, hb⟩ := hs'
            exact le_trans (hn b) (Finset.single_le_sum (fun c _ => Nat.zero_le _) hb)
          obtain ⟨K₁, hK₁le, h2⟩ := two_network_aux (∑ c ∈ s', w c) (w a) hw_sum (hw a)
            (∑ c ∈ s', n c) (n a) hn_sum (hn a) (∑ c ∈ s', m c) (m a) hm_sum (hm a) K
          obtain ⟨k', hk'out, hk'sum, hk'ineq⟩ := ih hs' K₁
          refine ⟨fun c => if c = a then K - K₁ else k' c, ?_, ?_, ?_⟩
          · intro c hc
            have hca : c ≠ a := fun h => hc (h ▸ Finset.mem_insert_self a s')
            have hcs : c ∉ s' := fun h => hc (Finset.mem_insert_of_mem h)
            simp only [hca, ↓reduceIte]
            exact hk'out c hcs
          · rw [Finset.sum_insert ha]
            have hsum' : (∑ c ∈ s', if c = a then K - K₁ else k' c) = ∑ c ∈ s', k' c := by
              apply Finset.sum_congr rfl
              intro c hc
              have hca : c ≠ a := fun h => ha (h ▸ hc)
              simp only [hca, ↓reduceIte]
            rw [hsum']
            simp only [↓reduceIte]
            omega
          · simp only [Finset.sum_insert ha]
            simp only [↓reduceIte]
            have hsum' : (∑ c ∈ s', w c * ((if c = a then K - K₁ else k' c : ℕ) : ℝ) /
                ((n c : ℝ) + ((if c = a then K - K₁ else k' c : ℕ) : ℝ) - 1 + m c))
                = ∑ c ∈ s', w c * k' c / ((n c : ℝ) + k' c - 1 + m c) := by
              apply Finset.sum_congr rfl
              intro c hc
              have hca : c ≠ a := fun h => ha (h ▸ hc)
              simp only [hca, ↓reduceIte]
            rw [hsum']
            have hcast : ((K - K₁ : ℕ) : ℝ) = (K:ℝ) - (K₁:ℝ) := Nat.cast_sub hK₁le
            rw [hcast]
            have hLHS : (w a + ∑ c ∈ s', w c) * (K:ℝ) /
                  (((n a : ℝ) + ∑ c ∈ s', (n c : ℝ)) + (K:ℝ) - 1 + (m a + ∑ c ∈ s', m c))
                = ((∑ c ∈ s', w c) + w a) * (K:ℝ) /
                  (((∑ c ∈ s', (n c : ℝ)) + (n a : ℝ)) + (K:ℝ) - 1 + ((∑ c ∈ s', m c) + m a)) := by
              congr 1 <;> ring
            rw [hLHS]
            simp only [Nat.cast_sum] at h2
            linarith [h2, hk'ineq]
        · have hs'empty : s' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
          subst hs'empty
          refine ⟨fun c => if c = a then K else 0, ?_, ?_, ?_⟩
          · intro c hc
            have hca : c ≠ a := fun h => hc (h ▸ Finset.mem_insert_self a ∅)
            simp only [hca, ↓reduceIte]
          · simp [Finset.sum_insert]
          · simp [Finset.sum_insert]
  obtain ⟨k, hkout, hksum, hkineq⟩ := key Finset.univ Finset.univ_nonempty K
  refine ⟨k, ?_, ?_⟩
  · simpa using hksum
  · simpa using hkineq
