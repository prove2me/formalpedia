-- Prove2me | solution 1 for TopDownParity1043.Main.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T14:34:38.389267+00:00
-- url     : https://prove2.me/submissions/9140b8fa-7cb2-47d2-8a0d-56b48ed746fd

import Mathlib
import Definitions.Def_TopDownParity1043_Main_HarmonicMean

set_option autoImplicit false
open scoped NNReal ENNReal
open TopDownParity1043.Main

theorem solution (A : Type) [Fintype A] (p g : A → ℝ≥0)
    (hp : ∀ z, 0 < p z) (hp1 : ∑ z, p z = 1) :
    weightedHarmonic p g =
      ⨅ (w : A → ℝ≥0) (_ : ∑ z, p z * w z = 1),
        (weightedEnergy p g w : ℝ≥0∞) := by
  classical
  by_cases hg0 : ∃ z, g z = 0
  · obtain ⟨z₀, hz₀⟩ := hg0
    have hsumtop :
        ∑ z, (p z : ℝ≥0∞) * (g z : ℝ≥0∞)⁻¹ = ∞ := by
      rw [ENNReal.sum_eq_top]
      refine ⟨z₀, Finset.mem_univ z₀, ?_⟩
      simp [hz₀, (hp z₀).ne']
    have hleft : weightedHarmonic p g = 0 := by
      simp [weightedHarmonic, hsumtop]
    let w : A → ℝ≥0 := fun z => if z = z₀ then (p z₀)⁻¹ else 0
    have hw : ∑ z, p z * w z = 1 := by
      simp [w, (hp z₀).ne']
    have henergy : weightedEnergy p g w = 0 := by
      apply Finset.sum_eq_zero
      intro z hz
      by_cases hzz : z = z₀
      · subst z
        simp [weightedEnergy, w, hz₀]
      · simp [weightedEnergy, w, hzz]
    rw [hleft]
    apply le_antisymm bot_le
    calc
      ⨅ (w : A → ℝ≥0) (_ : ∑ z, p z * w z = 1),
          (weightedEnergy p g w : ℝ≥0∞)
          ≤ ⨅ (_ : ∑ z, p z * w z = 1),
              (weightedEnergy p g w : ℝ≥0∞) := iInf_le _ w
      _ ≤ (weightedEnergy p g w : ℝ≥0∞) := iInf_le _ hw
      _ = 0 := by simp [henergy]
  · push_neg at hg0
    have huniv : (Finset.univ : Finset A).Nonempty := by
      by_contra h
      have he : (Finset.univ : Finset A) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp h
      have hbad : (0 : ℝ≥0) = 1 := by simpa [he] using hp1
      exact zero_ne_one hbad
    let S : ℝ≥0 := ∑ z, p z * (g z)⁻¹
    have hSpos : 0 < S := by
      apply Finset.sum_pos
      · intro z hz
        exact mul_pos (hp z) (inv_pos.mpr (pos_iff_ne_zero.mpr (hg0 z)))
      · exact huniv
    have hsumcoe :
        ∑ z, (p z : ℝ≥0∞) * (g z : ℝ≥0∞)⁻¹ = (S : ℝ≥0∞) := by
      simp only [S, ENNReal.coe_finset_sum, ENNReal.coe_mul]
      apply Finset.sum_congr rfl
      intro z hz
      rw [ENNReal.coe_inv (hg0 z)]
    have hleft : weightedHarmonic p g = (S⁻¹ : ℝ≥0) := by
      rw [weightedHarmonic, hsumcoe, ← ENNReal.coe_inv hSpos.ne']
    rw [hleft]
    apply le_antisymm
    · apply le_iInf
      intro w
      apply le_iInf
      intro hw
      apply ENNReal.coe_le_coe.mpr
      have htitu := Finset.sq_sum_div_le_sum_sq_div
        (R := ℝ≥0) Finset.univ (fun z => p z * w z)
        (g := fun z => p z * (g z)⁻¹)
        (fun z hz => mul_pos (hp z)
          (inv_pos.mpr (pos_iff_ne_zero.mpr (hg0 z))))
      have hterm : ∀ z,
          (p z * w z) ^ 2 / (p z * (g z)⁻¹) =
            p z * g z * w z ^ 2 := by
        intro z
        field_simp [(hp z).ne', hg0 z]
      calc
        S⁻¹ = (∑ z, p z * w z) ^ 2 / ∑ z, p z * (g z)⁻¹ := by
          rw [hw]
          simp [S]
        _ ≤ ∑ z, (p z * w z) ^ 2 / (p z * (g z)⁻¹) := htitu
        _ = weightedEnergy p g w := by
          apply Finset.sum_congr rfl
          intro z hz
          exact hterm z
    · let w : A → ℝ≥0 := fun z => S⁻¹ * (g z)⁻¹
      have hw : ∑ z, p z * w z = 1 := by
        rw [show ∑ z, p z * w z = S⁻¹ * S by
          simp only [w, S]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z hz
          ring]
        exact inv_mul_cancel₀ hSpos.ne'
      calc
        ⨅ (v : A → ℝ≥0) (_ : ∑ z, p z * v z = 1),
            (weightedEnergy p g v : ℝ≥0∞)
            ≤ ⨅ (_ : ∑ z, p z * w z = 1),
                (weightedEnergy p g w : ℝ≥0∞) := iInf_le _ w
        _ ≤ (weightedEnergy p g w : ℝ≥0∞) := iInf_le _ hw
        _ = (S⁻¹ : ℝ≥0) := by
          apply ENNReal.coe_inj.mpr
          rw [show weightedEnergy p g w = S⁻¹ ^ 2 * S by
            simp only [weightedEnergy, w, S]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z hz
            field_simp [hg0 z]]
          field_simp [hSpos.ne']
