-- Prove2me | solution 1 for UnderstandingML.weighted_majority_regret
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T13:22:27.814776+00:00
-- url     : https://prove2.me/submissions/2799e57e-1842-4f8c-8e3f-a27a28b90c38


import Definitions.Def_UnderstandingML_Online

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- `e^{-a} ≤ 1 - a + a²/2` for `a ≥ 0`. -/
theorem exp_neg_le_one_sub_add_sq (a : ℝ) (ha : 0 ≤ a) : Real.exp (-a) ≤ 1 - a + a ^ 2 / 2 := by
  have h1 := Real.quadratic_le_exp_of_nonneg ha
  have hpos : 0 < 1 + a + a ^ 2 / 2 := by positivity
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos a)]
  calc (1 : ℝ) ≤ (1 + a + a ^ 2 / 2) * (1 - a + a ^ 2 / 2) := by nlinarith [sq_nonneg (a ^ 2)]
    _ ≤ Real.exp a * (1 - a + a ^ 2 / 2) := by
        apply mul_le_mul_of_nonneg_right h1
        nlinarith [sq_nonneg (a - 1)]
    _ = (1 - a + a ^ 2 / 2) * Real.exp a := mul_comm _ _

/-- One step of the potential argument for Weighted-Majority: with
`Zₜ = ∑ⱼ exp(-η ∑_{s<t} v_{s,j})`, `log Z_{t+1} ≤ log Zₜ - η ⟨w⁽ᵗ⁾, vₜ⟩ + η²/2`. -/
theorem wm_log_potential_step {d : ℕ} (hd : 0 < d) (η : ℝ) (hη : 0 ≤ η)
    (v : ℕ → Fin d → ℝ) (hv : ∀ t i, v t i ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    Real.log (∑ j, Real.exp (-η * ∑ s ∈ Finset.range (t + 1), v s j)) ≤
      Real.log (∑ j, Real.exp (-η * ∑ s ∈ Finset.range t, v s j)) -
        η * ∑ i, wmWeights η v t i * v t i + η ^ 2 / 2 := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  set e : Fin d → ℝ := fun j ↦ Real.exp (-η * ∑ s ∈ Finset.range t, v s j) with he
  set Z := ∑ j, e j with hZ
  have hZpos : 0 < Z := Finset.sum_pos (fun j _ ↦ Real.exp_pos _) Finset.univ_nonempty
  set r := ∑ j, wmWeights η v t j * Real.exp (-η * v t j) with hr
  have hw : ∀ j, wmWeights η v t j = e j / Z := fun j ↦ rfl
  have hsplit : ∑ j, Real.exp (-η * ∑ s ∈ Finset.range (t + 1), v s j) = Z * r := by
    rw [hr, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hw, Finset.sum_range_succ, mul_add, Real.exp_add]
    simp only [he]
    field_simp
  have hrpos : 0 < r :=
    Finset.sum_pos (fun j _ ↦ mul_pos (div_pos (Real.exp_pos _) hZpos) (Real.exp_pos _))
      Finset.univ_nonempty
  have hwsum : ∑ j, wmWeights η v t j = 1 := by
    simp only [hw]
    rw [← Finset.sum_div, div_self hZpos.ne']
  have hr_le : r ≤ 1 - η * ∑ i, wmWeights η v t i * v t i + η ^ 2 / 2 := by
    calc r ≤ ∑ j, wmWeights η v t j * (1 - η * v t j + η ^ 2 / 2) := by
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_left _ (div_nonneg (Real.exp_pos _).le hZpos.le)
          obtain ⟨h0, h1⟩ := hv t j
          have := exp_neg_le_one_sub_add_sq (η * v t j) (mul_nonneg hη h0)
          rw [neg_mul]
          nlinarith [mul_nonneg (mul_nonneg hη hη) (mul_nonneg h0 (sub_nonneg.2 h1))]
      _ = (∑ j, wmWeights η v t j) - η * ∑ i, wmWeights η v t i * v t i +
            η ^ 2 / 2 * ∑ j, wmWeights η v t j := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = 1 - η * ∑ i, wmWeights η v t i * v t i + η ^ 2 / 2 := by rw [hwsum]; ring
  rw [hsplit, Real.log_mul hZpos.ne' hrpos.ne']
  have := Real.log_le_sub_one_of_pos hrpos
  linarith

/-- The core Weighted-Majority inequality: for every expert `i` and `η ≥ 0`,
`η (∑ₜ ⟨w⁽ᵗ⁾, vₜ⟩ - ∑ₜ v_{t,i}) ≤ log d + T η²/2`. -/
theorem wm_core {d : ℕ} (hd : 0 < d) (η : ℝ) (hη : 0 ≤ η)
    (v : ℕ → Fin d → ℝ) (hv : ∀ t i, v t i ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) (i : Fin d) :
    η * (∑ t ∈ Finset.range T, ∑ j, wmWeights η v t j * v t j -
        ∑ t ∈ Finset.range T, v t i) ≤ Real.log d + T * η ^ 2 / 2 := by
  set Φ : ℕ → ℝ := fun t ↦ Real.log (∑ j, Real.exp (-η * ∑ s ∈ Finset.range t, v s j))
    with hΦ
  have hΦ0 : Φ 0 = Real.log d := by simp [hΦ]
  have htel : Φ T - Φ 0 ≤ -η * ∑ t ∈ Finset.range T, ∑ j, wmWeights η v t j * v t j +
      T * η ^ 2 / 2 := by
    rw [← Finset.sum_range_sub]
    calc ∑ t ∈ Finset.range T, (Φ (t + 1) - Φ t)
        ≤ ∑ t ∈ Finset.range T, (-η * ∑ j, wmWeights η v t j * v t j + η ^ 2 / 2) := by
          apply Finset.sum_le_sum
          intro t _
          have := wm_log_potential_step hd η hη v hv t
          simp only [hΦ]
          linarith
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          simp
          ring
  have hlow : -η * ∑ t ∈ Finset.range T, v t i ≤ Φ T := by
    simp only [hΦ]
    rw [← Real.log_exp (-η * ∑ t ∈ Finset.range T, v t i)]
    apply Real.log_le_log (Real.exp_pos _)
    exact Finset.single_le_sum (f := fun j ↦ Real.exp (-η * ∑ s ∈ Finset.range T, v s j))
      (fun j _ ↦ (Real.exp_pos _).le) (Finset.mem_univ i)
  rw [hΦ0] at htel
  nlinarith

theorem weighted_majority_regret (d : ℕ) (hd : 0 < d) (T : ℕ) (hT : 2 * Real.log d < T)
    (v : ℕ → Fin d → ℝ) (hv : ∀ t i, v t i ∈ Set.Icc (0 : ℝ) 1) :
    ∑ t ∈ Finset.range T, ∑ i, wmWeights (Real.sqrt (2 * Real.log d / T)) v t i * v t i -
      ⨅ i, ∑ t ∈ Finset.range T, v t i ≤ Real.sqrt (2 * Real.log d * T) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i : Fin d ↦ ∑ t ∈ Finset.range T, v t i)
  rw [← hi]
  have hL0 : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
  have hTpos : (0 : ℝ) < T := by linarith
  rcases hL0.eq_or_lt with hL | hL
  · -- `d = 1`: the weights are uniform on a single expert and the regret is `0`.
    have hd1 : d = 1 := by
      have h := Real.eq_one_of_pos_of_log_eq_zero (by exact_mod_cast hd) hL.symm
      exact_mod_cast h
    subst hd1
    rw [← hL]
    simp only [mul_zero, zero_div, Real.sqrt_zero, zero_mul]
    have hw : ∀ t (j : Fin 1), wmWeights 0 v t j = 1 := by
      intro t j
      simp [wmWeights]
    simp only [hw, one_mul]
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simp
  · set L := Real.log d
    set η := Real.sqrt (2 * L / T) with hηdef
    have hηpos : 0 < η := Real.sqrt_pos.2 (by positivity)
    have hη2 : η ^ 2 = 2 * L / T := Real.sq_sqrt (by positivity)
    have hcore := wm_core hd η hηpos.le v hv T i
    have hTη : (T : ℝ) * η ^ 2 / 2 = L := by rw [hη2]; field_simp
    have hprod : η * Real.sqrt (2 * L * T) = 2 * L := by
      rw [hηdef, ← Real.sqrt_mul (by positivity)]
      have : 2 * L / T * (2 * L * T) = (2 * L) ^ 2 := by field_simp
      rw [this, Real.sqrt_sq (by positivity)]
    rw [hTη] at hcore
    have : η * (∑ t ∈ Finset.range T, ∑ j, wmWeights η v t j * v t j -
        ∑ t ∈ Finset.range T, v t i) ≤ η * Real.sqrt (2 * L * T) := by linarith
    exact le_of_mul_le_mul_left this hηpos

end UnderstandingML

open UnderstandingML in
theorem solution (d : ℕ) (hd : 0 < d) (T : ℕ) (hT : 2 * Real.log d < T)
    (v : ℕ → Fin d → ℝ) (hv : ∀ t i, v t i ∈ Set.Icc (0 : ℝ) 1) :
    ∑ t ∈ Finset.range T, ∑ i, wmWeights (Real.sqrt (2 * Real.log d / T)) v t i * v t i -
      ⨅ i, ∑ t ∈ Finset.range T, v t i ≤ Real.sqrt (2 * Real.log d * T) := by
  apply UnderstandingML.weighted_majority_regret <;> assumption
