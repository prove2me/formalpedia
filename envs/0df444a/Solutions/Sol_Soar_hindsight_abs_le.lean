-- Prove2me | solution 1 for Soar.hindsight_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T00:18:50.287745+00:00
-- url     : https://prove2.me/submissions/7bd5410d-8ae2-4952-bfb1-26332e7fe094

import Mathlib
import Definitions.Def_SoarModel

open MeasureTheory

namespace SoarAux

lemma sum_abs_le {X Y : Type*} (φ : X → Y → ℝ) (C : ℝ) (hC : SoarBounded φ C) {n : ℕ}
    (x : Fin n → X) (y : Fin n → Y) (σ : Equiv.Perm (Fin n)) :
    |∑ t : Fin n, φ (x t) (y (σ t))| ≤ n * C := by
  calc |∑ t : Fin n, φ (x t) (y (σ t))| ≤ ∑ t : Fin n, |φ (x t) (y (σ t))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : Fin n, C := Finset.sum_le_sum fun t _ => hC _ _
    _ = n * C := by simp

lemma hs_abs_le {X Y : Type*} (φ : X → Y → ℝ) (C : ℝ) (hC : SoarBounded φ C) {n : ℕ}
    (x : Fin n → X) (y : Fin n → Y) : |SoarHindsightSum φ x y| ≤ n * C := by
  unfold SoarHindsightSum
  have hb : BddAbove (Set.range fun σ : Equiv.Perm (Fin n) => ∑ t : Fin n, φ (x t) (y (σ t))) :=
    (Set.finite_range _).bddAbove
  rw [abs_le]
  constructor
  · have h1 := (abs_le.mp (sum_abs_le φ C hC x y 1)).1
    exact le_trans h1 (le_ciSup hb 1)
  · exact ciSup_le fun σ => (abs_le.mp (sum_abs_le φ C hC x y σ)).2

end SoarAux

open SoarAux in
theorem solution {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (C : ℝ) (hC : SoarBounded φ C) :
    (∀ n : ℕ, |SoarHindsight P Q φ n| ≤ C) ∧ |SoarLimit P Q φ| ≤ C := by
  -- `C ≥ 0` since the spaces are nonempty (they carry probability measures)
  have hX : Nonempty X := nonempty_of_isProbabilityMeasure P
  have hY : Nonempty Y := nonempty_of_isProbabilityMeasure Q
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC (Classical.arbitrary X) (Classical.arbitrary Y))
  have hH : ∀ n : ℕ, |SoarHindsight P Q φ n| ≤ C := by
    intro n
    unfold SoarHindsight
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hC0]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [abs_div, abs_of_pos hnR, div_le_iff₀ hnR]
    haveI : IsProbabilityMeasure (SoarPairMeasure P Q n) := by
      unfold SoarPairMeasure; infer_instance
    have hint : ‖∫ p, SoarHindsightSum φ p.1 p.2 ∂SoarPairMeasure P Q n‖ ≤
        (n * C) * (SoarPairMeasure P Q n).real Set.univ :=
      norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]; exact hs_abs_le φ C hC p.1 p.2)
    have hprob : (SoarPairMeasure P Q n).real Set.univ = 1 := by simp
    rw [hprob, mul_one, Real.norm_eq_abs] at hint
    linarith
  refine ⟨hH, ?_⟩
  unfold SoarLimit
  have hb : BddAbove (Set.range fun n : ℕ => SoarHindsight P Q φ (n + 1)) :=
    ⟨C, by rintro _ ⟨n, rfl⟩; exact (abs_le.mp (hH (n + 1))).2⟩
  rw [abs_le]
  constructor
  · exact le_trans (abs_le.mp (hH 1)).1 (le_ciSup hb 0)
  · exact ciSup_le fun n => (abs_le.mp (hH (n + 1))).2
