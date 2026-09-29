-- Prove2me | solution 1 for Soar.hindsight_dominates
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T02:16:23.788777+00:00
-- url     : https://prove2.me/submissions/6fc69f23-9a59-4080-a992-1009d4a66890

import Mathlib
import Definitions.Def_SoarModel

open MeasureTheory

namespace SoarAux2

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
  · exact le_trans (abs_le.mp (sum_abs_le φ C hC x y 1)).1 (le_ciSup hb 1)
  · exact ciSup_le fun σ => (abs_le.mp (sum_abs_le φ C hC x y σ)).2

lemma term_meas {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (φ : X → Y → ℝ)
    (hφ : Measurable (Function.uncurry φ)) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Measurable (fun p : (Fin n → X) × (Fin n → Y) => ∑ t : Fin n, φ (p.1 t) (p.2 (σ t))) := by
  apply Finset.measurable_sum
  intro t _
  have h1 : Measurable (fun p : (Fin n → X) × (Fin n → Y) => (p.1 t, p.2 (σ t))) :=
    ((measurable_pi_apply t).comp measurable_fst).prodMk ((measurable_pi_apply (σ t)).comp measurable_snd)
  exact hφ.comp h1

lemma hs_meas {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (φ : X → Y → ℝ)
    (hφ : Measurable (Function.uncurry φ)) (n : ℕ) :
    Measurable (fun p : (Fin n → X) × (Fin n → Y) => SoarHindsightSum φ p.1 p.2) := by
  unfold SoarHindsightSum
  exact Measurable.iSup fun σ => term_meas φ hφ σ

end SoarAux2

open SoarAux2 in
theorem solution {X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Ω] (P : Measure X) (Q : Measure Y) (μ : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure μ]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (C : ℝ) (hC : SoarBounded φ C)
    (n : ℕ) (τ : (Fin n → X) × (Fin n → Y) → Ω → Equiv.Perm (Fin n))
    (hτ : Measurable (Function.uncurry τ)) :
    (∫ q, ∑ t, φ (q.1.1 t) (q.1.2 (τ q.1 q.2 t)) ∂(SoarPairMeasure P Q n).prod μ) / n
      ≤ SoarHindsight P Q φ n := by
  have : IsProbabilityMeasure (SoarPairMeasure P Q n) := by
    unfold SoarPairMeasure; infer_instance
  unfold SoarHindsight
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  -- measurability of the randomized assignment value
  have hG : Measurable (fun r : ((Fin n → X) × (Fin n → Y)) × Equiv.Perm (Fin n) =>
      ∑ t : Fin n, φ (r.1.1 t) (r.1.2 (r.2 t))) :=
    measurable_from_prod_countable_left fun σ => term_meas φ hφ σ
  have hf : Measurable (fun q : ((Fin n → X) × (Fin n → Y)) × Ω =>
      ∑ t, φ (q.1.1 t) (q.1.2 (τ q.1 q.2 t))) :=
    hG.comp (measurable_fst.prodMk hτ)
  have hHS := hs_meas φ hφ n
  have hint1 : Integrable (fun q : ((Fin n → X) × (Fin n → Y)) × Ω =>
      ∑ t, φ (q.1.1 t) (q.1.2 (τ q.1 q.2 t))) ((SoarPairMeasure P Q n).prod μ) :=
    Integrable.of_bound hf.aestronglyMeasurable (n * C) (Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs]; exact sum_abs_le φ C hC q.1.1 q.1.2 (τ q.1 q.2))
  have hint2 : Integrable (fun q : ((Fin n → X) × (Fin n → Y)) × Ω =>
      SoarHindsightSum φ q.1.1 q.1.2) ((SoarPairMeasure P Q n).prod μ) :=
    Integrable.of_bound (hHS.comp measurable_fst).aestronglyMeasurable (n * C)
      (Filter.Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs]; exact hs_abs_le φ C hC q.1.1 q.1.2)
  calc ∫ q, ∑ t, φ (q.1.1 t) (q.1.2 (τ q.1 q.2 t)) ∂(SoarPairMeasure P Q n).prod μ
      ≤ ∫ q, SoarHindsightSum φ q.1.1 q.1.2 ∂(SoarPairMeasure P Q n).prod μ := by
        apply integral_mono hint1 hint2
        intro q
        dsimp only
        unfold SoarHindsightSum
        exact le_ciSup (f := fun σ : Equiv.Perm (Fin n) => ∑ t, φ (q.1.1 t) (q.1.2 (σ t)))
          (Set.finite_range _).bddAbove (τ q.1 q.2)
    _ = ∫ p, SoarHindsightSum φ p.1 p.2 ∂SoarPairMeasure P Q n := by
        rw [integral_prod _ hint2]
        simp
