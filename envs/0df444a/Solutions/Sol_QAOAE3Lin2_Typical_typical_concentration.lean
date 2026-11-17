-- Prove2me | solution 1 for QAOAE3Lin2.Typical.typical_concentration
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T12:44:39.382831+00:00
-- url     : https://prove2.me/submissions/1c8d580e-0199-43d6-aef4-621465d1362a

import Definitions.Def_QAOAE3Lin2_Typical_Setting
import Theorems.Thm_QAOAE3Lin2_Typical_eq_50
import Theorems.Thm_QAOAE3Lin2_Typical_variance_bound

open QAOAE3Lin2.Typical

theorem solution {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (D : ℕ)
    (htri : QAOAE3Lin2.General.IsTripleFamily tri)
    (hocc : QAOAE3Lin2.General.BoundedOccurrence tri D)
    (γ : ℝ) (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ Real.pi / 2) (t : ℝ) (ht : 0 < t) :
    ((Finset.univ.filter fun rhs : Fin m → Bool =>
        QAOAE3Lin2.General.expSat tri rhs (-γ) (Real.pi / 4) ≤
          (m : ℝ) / 2 + (m : ℝ) / 2 * Real.sin γ * Real.cos γ ^ (3 * D) - t).card : ℝ) / 2 ^ m ≤
      (m : ℝ) * (6 * D + 3) * (D + 1) / (4 * t ^ 2) := by
  let g : (Fin m → Bool) → ℝ := fun rhs => QAOAE3Lin2.General.expSat tri rhs (-γ) (Real.pi / 4)
  let thr : ℝ := (m : ℝ) / 2 + (m : ℝ) / 2 * Real.sin γ * Real.cos γ ^ (3 * D)
  let S : Finset (Fin m → Bool) := Finset.univ.filter fun rhs : Fin m → Bool => g rhs ≤ thr - t
  have hmean := (QAOAE3Lin2.Typical.eq_50 tri D htri hocc γ hγ₀ hγ₁).1
  have hvar := QAOAE3Lin2.Typical.variance_bound tri D htri hocc γ
  have havg_sub :
      avgD (fun rhs => g rhs - (m : ℝ) / 2) = avgD g - (m : ℝ) / 2 := by
    have h2 : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
    have hcard : (Fintype.card (Fin m → Bool) : ℝ) = (2 : ℝ) ^ m := by
      simp [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    simp only [avgD]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, mul_sub,
      ← mul_assoc, inv_mul_cancel₀ h2, one_mul]
  have hthr_le_avg : thr ≤ avgD g := by
    dsimp [thr]
    linarith [hmean, havg_sub]
  have hterm : ∀ rhs ∈ S, t ^ 2 ≤ (g rhs - avgD g) ^ 2 := by
    intro rhs hrhs
    have hle : g rhs ≤ thr - t := (Finset.mem_filter.mp hrhs).2
    have hdiff : t ≤ avgD g - g rhs := by linarith
    have hsq : t ^ 2 ≤ (avgD g - g rhs) ^ 2 := by nlinarith
    have heq : (g rhs - avgD g) ^ 2 = (avgD g - g rhs) ^ 2 := by ring
    rw [heq]; exact hsq
  have hsum_le : (S.card : ℝ) * t ^ 2 ≤ ∑ rhs : Fin m → Bool, (g rhs - avgD g) ^ 2 := by
    calc
      (S.card : ℝ) * t ^ 2 = ∑ _rhs ∈ S, t ^ 2 := by simp [nsmul_eq_mul]
      _ ≤ ∑ rhs ∈ S, (g rhs - avgD g) ^ 2 := Finset.sum_le_sum hterm
      _ ≤ ∑ rhs : Fin m → Bool, (g rhs - avgD g) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun _ _ _ => sq_nonneg _)
  have h2m_pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have ht2_pos : (0 : ℝ) < t ^ 2 := by positivity
  have hcheb : (S.card : ℝ) / (2 : ℝ) ^ m * t ^ 2 ≤ varD g := by
    rw [varD, avgD]
    rw [div_mul_eq_mul_div, div_le_iff₀ h2m_pos, mul_comm ((2 ^ m : ℝ)⁻¹), ← div_eq_mul_inv,
      div_mul_cancel₀ _ h2m_pos.ne']
    exact hsum_le
  have hcheb' : (S.card : ℝ) / (2 : ℝ) ^ m ≤ varD g / t ^ 2 := (le_div_iff₀ ht2_pos).mpr hcheb
  have hvar_div : varD g / t ^ 2 ≤ (m : ℝ) * (6 * D + 3) * (D + 1) / (4 * t ^ 2) := by
    calc
      varD g / t ^ 2 ≤ ((m : ℝ) * (6 * D + 3) * (D + 1) / 4) / t ^ 2 :=
        div_le_div_of_nonneg_right hvar ht2_pos.le
      _ = (m : ℝ) * (6 * D + 3) * (D + 1) / (4 * t ^ 2) := by ring
  exact hcheb'.trans hvar_div
