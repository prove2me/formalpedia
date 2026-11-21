-- Prove2me | solution 1 for PalomarNewtonian.globalCubicSensitivityAndOptimality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:24:37.137894+00:00
-- url     : https://prove2.me/submissions/58542db5-f400-4f00-acb7-caf17724cb1d

module
public import Definitions.Def_NewtonianLipschitz
public import Definitions.Def_NewtonianLipschitz_Solution_74f12a8
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_eq_formula
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_cons
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_nil
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_gravitationalParameter_eq_one
public import Theorems.Thm_NewtonianLipschitz_candidateCoefficient_eq
public import Theorems.Thm_NewtonianLipschitz_candidateCriticalPoint_spec
public import Theorems.Thm_NewtonianLipschitz_candidateMaximum_eq
public import Theorems.Thm_NewtonianLipschitz_candidateMaximum_nonneg
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_one
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_two
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_zero
public import Theorems.Thm_NewtonianLipschitz_cycleVec_one
public import Theorems.Thm_NewtonianLipschitz_cycleVec_two
public import Theorems.Thm_NewtonianLipschitz_cycleVec_zero
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_eq_coordinates
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_one
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_two
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_zero
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_oneSourceGlobalCandidateBound_proved
public import Theorems.Thm_NewtonianLipschitz_stationaryCubic_eq
public import Theorems.Thm_NewtonianLipschitz_stationaryCubic_root_unique_on_unitInterval
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_one
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_two
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_zero
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_one
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_two
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_zero
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
public import Theorems.Thm_NewtonianLipschitz_unitSource_safe_global_bound_iff_candidateMaximum_le
attribute [local simp] NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_cons
attribute [local simp] NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_nil
attribute [local simp] NewtonianLipschitz.coordinateAbs_apply
attribute [local simp] NewtonianLipschitz.cycleIndex_one
attribute [local simp] NewtonianLipschitz.cycleIndex_two
attribute [local simp] NewtonianLipschitz.cycleIndex_zero
attribute [local simp] NewtonianLipschitz.cycleVec_one
attribute [local simp] NewtonianLipschitz.cycleVec_two
attribute [local simp] NewtonianLipschitz.cycleVec_zero
attribute [local simp] NewtonianLipschitz.normalizedVector_one
attribute [local simp] NewtonianLipschitz.normalizedVector_two
attribute [local simp] NewtonianLipschitz.normalizedVector_zero
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.swapYZIndex_one
attribute [local simp] NewtonianLipschitz.swapYZIndex_two
attribute [local simp] NewtonianLipschitz.swapYZIndex_zero
attribute [local simp] NewtonianLipschitz.swapYZVec_one
attribute [local simp] NewtonianLipschitz.swapYZVec_two
attribute [local simp] NewtonianLipschitz.swapYZVec_zero
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero


section
public section
open NewtonianLipschitz
private theorem physicalFiniteSourceGlobalBound
    (n : ℕ) (G M d : ℝ)
    (m : Fin n → ℝ) (a : Fin n → Fin 3 → ℝ)
    (P Q : Fin 3 → ℝ)
    (hG : 0 ≤ G) (hM : 0 ≤ M) (hd : 0 < d)
    (hm : ∀ i : Fin n, 0 ≤ m i ∧ m i ≤ M)
    (hs : ∀ i : Fin n, d ≤ ‖P - a i‖ ∧ d ≤ ‖Q - a i‖) :
    let g : (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
      fun z =>
        ∑ i : Fin n,
          (-(G * m i) /
            (Real.sqrt
              ((z 0 - a i 0) ^ 2 +
               (z 1 - a i 1) ^ 2 +
               (z 2 - a i 2) ^ 2)) ^ 3) • (z - a i)
    ‖g P - g Q‖ ≤
      ((n : ℝ) * G * M * candidateMaximum / d ^ 3) * ‖P - Q‖ := by
  let term : Fin n → Vec3 → Vec3 := fun i z =>
    (-(G * m i) /
      (Real.sqrt
        ((z 0 - a i 0) ^ 2 +
         (z 1 - a i 1) ^ 2 +
         (z 2 - a i 2) ^ 2)) ^ 3) • (z - a i)
  let g : Vec3 → Vec3 := fun z => ∑ i : Fin n, term i z
  have hterm (i : Fin n) :
      ‖term i P - term i Q‖ ≤
        ((1 / d ^ 3) * ((G * m i) * candidateMaximum)) *
          ‖P - Q‖ := by
    let c : NewtonianPointSource :=
      { gravitationalParameter := G * m i
        gravitationalParameter_nonneg := mul_nonneg hG (hm i).1
        displacement := NewtonianPointSource.unitAxis.displacement
        displacement_ne_zero :=
          NewtonianPointSource.unitAxis.displacement_ne_zero }
    have hcμ : c.gravitationalParameter = G * m i := by
      rfl
    have hident (z : Vec3) :
        term i z = c.accelerationField (z - a i) := by
      dsimp [term]
      rw [c.accelerationField_eq_formula, hcμ,
        euclideanRadius_eq_coordinates]
      simp only [Pi.sub_apply]
    have hdist : (P - a i) - (Q - a i) = P - Q := by
      abel
    have hsingle :=
      oneSourceGlobalCandidateBound_proved
        c (P - a i) (Q - a i) d hd (hs i).1 (hs i).2
    calc
      ‖term i P - term i Q‖ =
          ‖c.accelerationField (P - a i) -
            c.accelerationField (Q - a i)‖ := by
          rw [hident, hident]
      _ ≤ ((1 / d ^ 3) *
             ((G * m i) * candidateMaximum)) *
            ‖(P - a i) - (Q - a i)‖ := by
          simpa only [hcμ] using hsingle
      _ = ((1 / d ^ 3) * ((G * m i) *
            candidateMaximum)) * ‖P - Q‖ := by
          rw [hdist]
  have hmass :
      (∑ i : Fin n, G * m i) ≤ (n : ℝ) * (G * M) := by
    have hmasses :
        (∑ i : Fin n, m i) ≤ (n : ℝ) * M := by
      calc
        (∑ i : Fin n, m i) ≤ ∑ _i : Fin n, M :=
          Finset.sum_le_sum (by
            intro i hi
            exact (hm i).2)
        _ = (n : ℝ) * M := by simp
    calc
      (∑ i : Fin n, G * m i) =
          G * (∑ i : Fin n, m i) := by
            rw [Finset.mul_sum]
      _ ≤ G * ((n : ℝ) * M) :=
        mul_le_mul_of_nonneg_left hmasses hG
      _ = (n : ℝ) * (G * M) := by ring
  have hcoefNonneg :
      0 ≤ (1 / d ^ 3) * candidateMaximum * ‖P - Q‖ := by
    exact mul_nonneg
      (mul_nonneg (by positivity) candidateMaximum_nonneg)
      (norm_nonneg _)
  have hsum :
      ‖g P - g Q‖ ≤
        ((n : ℝ) * G * M * candidateMaximum / d ^ 3) *
          ‖P - Q‖ := by
    calc
      ‖g P - g Q‖ =
          ‖∑ i : Fin n, (term i P - term i Q)‖ := by
            dsimp [g]
            rw [Finset.sum_sub_distrib]
      _ ≤ ∑ i : Fin n, ‖term i P - term i Q‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i : Fin n,
            ((1 / d ^ 3) * ((G * m i) *
              candidateMaximum)) * ‖P - Q‖ :=
        Finset.sum_le_sum (by intro i hi; exact hterm i)
      _ = ((∑ i : Fin n, G * m i) *
            ((1 / d ^ 3) * candidateMaximum * ‖P - Q‖)) := by
        calc
          _ = ∑ i : Fin n,
                (G * m i) *
                  ((1 / d ^ 3) * candidateMaximum *
                    ‖P - Q‖) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = _ := by rw [Finset.sum_mul]
      _ ≤ ((n : ℝ) * (G * M)) *
            ((1 / d ^ 3) * candidateMaximum * ‖P - Q‖) :=
        mul_le_mul_of_nonneg_right hmass hcoefNonneg
      _ = ((n : ℝ) * G * M *
            candidateMaximum / d ^ 3) * ‖P - Q‖ := by ring
  exact hsum
end
end

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace PalomarNewtonian
theorem _root_.solution
    (t : ℝ)
    (htlow : (9 / 50 : ℝ) ≤ t)
    (hthigh : t ≤ (1 / 5 : ℝ))
    (htcubic : 2 * t ^ 3 - 8 * t ^ 2 - 4 * t + 1 = 0) :
    (∀ (n : ℕ) (G M d : ℝ)
      (m : Fin n → ℝ) (a : Fin n → Fin 3 → ℝ)
      (P Q : Fin 3 → ℝ),
      0 ≤ G →
      0 ≤ M →
      0 < d →
      (∀ i : Fin n, 0 ≤ m i ∧ m i ≤ M) →
      (∀ i : Fin n, d ≤ ‖P - a i‖ ∧ d ≤ ‖Q - a i‖) →
      let g : (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
        fun z =>
          ∑ i : Fin n,
            (-(G * m i) /
              (Real.sqrt
                ((z 0 - a i 0) ^ 2 +
                 (z 1 - a i 1) ^ 2 +
                 (z 2 - a i 2) ^ 2)) ^ 3) • (z - a i)
      ‖g P - g Q‖ ≤
        ((n : ℝ) * G * M *
          ((2 + 6 * t - 2 * t ^ 2) /
            (Real.sqrt (1 + 2 * t ^ 2)) ^ 5) / d ^ 3) *
          ‖P - Q‖) ∧
    (∀ K : ℝ,
      (∀ P Q : Fin 3 → ℝ,
        (1 : ℝ) ≤ ‖P‖ →
        (1 : ℝ) ≤ ‖Q‖ →
        ‖(-(1 : ℝ) /
            (Real.sqrt (P 0 ^ 2 + P 1 ^ 2 + P 2 ^ 2)) ^ 3) • P -
          (-(1 : ℝ) /
            (Real.sqrt (Q 0 ^ 2 + Q 1 ^ 2 + Q 2 ^ 2)) ^ 3) • Q‖ ≤
          K * ‖P - Q‖) ↔
      (2 + 6 * t - 2 * t ^ 2) /
        (Real.sqrt (1 + 2 * t ^ 2)) ^ 5 ≤ K) := by
  have ht : t = candidateCriticalPoint := by
    apply stationaryCubic_root_unique_on_unitInterval
      t candidateCriticalPoint
      ⟨by linarith, by linarith⟩
      ⟨by
        have hs := candidateCriticalPoint_spec
        linarith [hs.1],
        by
        have hs := candidateCriticalPoint_spec
        linarith [hs.2.1]⟩
    · simpa only [stationaryCubic_eq] using htcubic
    · exact candidateCriticalPoint_spec.2.2
  have hC :
      candidateMaximum =
        (2 + 6 * t - 2 * t ^ 2) /
          (Real.sqrt (1 + 2 * t ^ 2)) ^ 5 := by
    rw [ht, candidateMaximum_eq, candidateCoefficient_eq]
  constructor
  · intro n G M d m a P Q hG hM hd hm hs
    have hbound := physicalFiniteSourceGlobalBound
      n G M d m a P Q hG hM hd hm hs
    calc
      _ ≤ ((n : ℝ) * G * M * candidateMaximum / d ^ 3) *
          ‖P - Q‖ := hbound
      _ = ((n : ℝ) * G * M *
            ((2 + 6 * t - 2 * t ^ 2) /
              (Real.sqrt (1 + 2 * t ^ 2)) ^ 5) / d ^ 3) *
          ‖P - Q‖ := by rw [hC]
  · intro K
    have hunit (z : Vec3) :
        (-(1 : ℝ) /
          (Real.sqrt (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2)) ^ 3) • z =
          NewtonianPointSource.unitAxis.accelerationField z := by
      rw [NewtonianPointSource.accelerationField_eq_formula,
        NewtonianPointSource.unitAxis_gravitationalParameter_eq_one,
        euclideanRadius_eq_coordinates]
    simpa only [← hunit, hC] using
      (unitSource_safe_global_bound_iff_candidateMaximum_le K)
end PalomarNewtonian
