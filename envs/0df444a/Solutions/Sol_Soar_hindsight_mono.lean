-- Prove2me | solution 1 for Soar.hindsight_mono
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T11:56:54.661342+00:00
-- url     : https://prove2.me/submissions/95077a6e-e7a9-476d-92bc-b496fae8f514

import Mathlib
import Definitions.Def_SoarModel

set_option autoImplicit false

open MeasureTheory

namespace SoarMonoAux

theorem meas_F {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (m : ℕ) :
    Measurable (fun p : (Fin m → X) × (Fin m → Y) => SoarHindsightSum φ p.1 p.2) := by
  unfold SoarHindsightSum
  refine Measurable.iSup fun σ => Finset.measurable_sum _ fun t _ => ?_
  have h : Measurable fun p : (Fin m → X) × (Fin m → Y) =>
      Function.uncurry φ (p.1 t, p.2 (σ t)) :=
    hφ.comp (((measurable_pi_apply t).comp measurable_fst).prodMk
      ((measurable_pi_apply (σ t)).comp measurable_snd))
  exact h

theorem bound_F {X Y : Type*} (φ : X → Y → ℝ) (C : ℝ) (hC : SoarBounded φ C) {m : ℕ}
    (x : Fin m → X) (y : Fin m → Y) : |SoarHindsightSum φ x y| ≤ m * C := by
  have hb : ∀ σ : Equiv.Perm (Fin m), |∑ t, φ (x t) (y (σ t))| ≤ m * C := by
    intro σ
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ t, |φ (x t) (y (σ t))| ≤ ∑ _t : Fin m, C := Finset.sum_le_sum fun t _ => hC _ _
      _ = m * C := by simp
  unfold SoarHindsightSum
  rw [abs_le]
  constructor
  · refine le_trans ?_ (le_ciSup (Set.finite_range fun σ : Equiv.Perm (Fin m) =>
      ∑ t, φ (x t) (y (σ t))).bddAbove 1)
    exact (abs_le.1 (hb 1)).1
  · exact ciSup_le fun σ => (abs_le.1 (hb σ)).2

theorem integrable_F {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (C : ℝ) (hC : SoarBounded φ C)
    (m : ℕ) {μ : Measure ((Fin m → X) × (Fin m → Y))} [IsFiniteMeasure μ] :
    Integrable (fun p : (Fin m → X) × (Fin m → Y) => SoarHindsightSum φ p.1 p.2) μ :=
  Integrable.of_bound (meas_F φ hφ m).aestronglyMeasurable (m * C)
    (Filter.Eventually.of_forall fun p => by
      simpa [Real.norm_eq_abs] using bound_F φ C hC p.1 p.2)

theorem remove_mp {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    {n : ℕ} (k : Fin (n + 1)) :
    MeasurePreserving (fun x : Fin (n + 1) → X => fun j => x (k.succAbove j))
      (Measure.pi fun _ => P) (Measure.pi fun _ => P) := by
  have h := (measurePreserving_snd (μ := P) (ν := Measure.pi fun _ : Fin n => P)).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) k)
  exact h

theorem perm_le {X Y : Type*} (φ : X → Y → ℝ) {m : ℕ} (x : Fin m → X) (y : Fin m → Y)
    (σ : Equiv.Perm (Fin m)) : ∑ t, φ (x t) (y (σ t)) ≤ SoarHindsightSum φ x y :=
  le_ciSup (Set.finite_range fun σ : Equiv.Perm (Fin m) => ∑ t, φ (x t) (y (σ t))).bddAbove σ

theorem ds_le {X Y : Type*} (φ : X → Y → ℝ) {m : ℕ} (x : Fin m → X) (y : Fin m → Y)
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A ∈ doublyStochastic ℝ (Fin m)) :
    ∑ i, ∑ j, A i j * φ (x i) (y j) ≤ SoarHindsightSum φ x y := by
  rw [← SetLike.mem_coe, doublyStochastic_eq_convexHull_permMatrix] at hA
  have hconv : Convex ℝ {B : Matrix (Fin m) (Fin m) ℝ |
      ∑ i, ∑ j, B i j * φ (x i) (y j) ≤ SoarHindsightSum φ x y} := by
    intro a ha b hb s t hs ht hst
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    have : ∑ i, ∑ j, (s • a + t • b) i j * φ (x i) (y j)
        = s * ∑ i, ∑ j, a i j * φ (x i) (y j) + t * ∑ i, ∑ j, b i j * φ (x i) (y j) := by
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
        Finset.mul_sum, mul_assoc]
    rw [this]
    calc s * ∑ i, ∑ j, a i j * φ (x i) (y j) + t * ∑ i, ∑ j, b i j * φ (x i) (y j)
        ≤ s * SoarHindsightSum φ x y + t * SoarHindsightSum φ x y :=
          add_le_add (mul_le_mul_of_nonneg_left ha hs) (mul_le_mul_of_nonneg_left hb ht)
      _ = SoarHindsightSum φ x y := by rw [← add_mul, hst, one_mul]
  refine convexHull_min ?_ hconv hA
  rintro _ ⟨σ, rfl⟩
  simp only [Set.mem_ofPred_eq]
  refine le_trans (le_of_eq ?_) (perm_le φ x y σ)
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, ite_mul, Finset.sum_ite_eq]

theorem core {X Y : Type*} (φ : X → Y → ℝ) {n : ℕ} (hn : 1 ≤ n)
    (x : Fin (n + 1) → X) (y : Fin (n + 1) → Y) :
    ∑ k : Fin (n + 1), SoarHindsightSum φ (fun j => x (k.succAbove j)) (fun j => y (k.succAbove j))
      ≤ n * SoarHindsightSum φ x y := by
  have hex : ∀ k : Fin (n + 1), ∃ σ : Equiv.Perm (Fin n),
      ∑ t, φ (x (k.succAbove t)) (y (k.succAbove (σ t)))
        = SoarHindsightSum φ (fun j => x (k.succAbove j)) (fun j => y (k.succAbove j)) :=
    fun k => exists_eq_ciSup_of_finite
  choose σ hσ using hex
  let τ : Fin (n + 1) → Equiv.Perm (Fin (n + 1)) := fun k =>
    (finSuccEquiv' k).symm.permCongr (Equiv.optionCongr (σ k))
  have hτk : ∀ k, τ k k = k := by
    intro k
    simp [τ, Equiv.permCongr_apply, finSuccEquiv'_at]
  have hτs : ∀ k t, τ k (k.succAbove t) = k.succAbove (σ k t) := by
    intro k t
    simp [τ, Equiv.permCongr_apply, finSuccEquiv'_succAbove, finSuccEquiv'_symm_some]
  have key : ∀ k, SoarHindsightSum φ (fun j => x (k.succAbove j)) (fun j => y (k.succAbove j))
      = ∑ i, φ (x i) (y (τ k i)) - φ (x k) (y k) := by
    intro k
    rw [← hσ k, Fin.sum_univ_succAbove _ k, hτk]
    simp [hτs]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  let D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j =>
    (n : ℝ)⁻¹ * ∑ k, ((if τ k i = j then (1 : ℝ) else 0) - (if i = k ∧ j = k then 1 else 0))
  have hD : D ∈ doublyStochastic ℝ (Fin (n + 1)) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
    · refine mul_nonneg (inv_nonneg.2 hnpos.le) (Finset.sum_nonneg fun k _ => ?_)
      by_cases h : i = k ∧ j = k
      · obtain ⟨rfl, rfl⟩ := h
        simp [hτk]
      · simp only [h, if_false, sub_zero]
        split_ifs <;> norm_num
    · simp only [D, ← Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      simp [ite_and, Finset.sum_ite_eq', Finset.sum_const]
      field_simp
    · simp only [D, ← Finset.mul_sum]
      rw [Finset.sum_comm]
      have h1 : ∀ k : Fin (n + 1), ∑ i, (if τ k i = j then (1 : ℝ) else 0) = 1 := by
        intro k
        have : ∀ i, (τ k i = j ↔ i = (τ k).symm j) := fun i => by
          constructor
          · rintro rfl; simp
          · rintro rfl; simp
        simp [this]
      simp only [Finset.sum_sub_distrib, h1]
      simp [ite_and, Finset.sum_ite_eq', Finset.sum_const]
      field_simp
  have hL := ds_le φ x y D hD
  have hk : ∀ k, ∑ i, ∑ j, ((if τ k i = j then (1 : ℝ) else 0) - (if i = k ∧ j = k then 1 else 0))
      * φ (x i) (y j) = ∑ i, φ (x i) (y (τ k i)) - φ (x k) (y k) := by
    intro k
    simp [sub_mul, Finset.sum_sub_distrib, ite_and, Finset.sum_ite_eq']
  have hcomp : ∑ i, ∑ j, D i j * φ (x i) (y j)
      = (n : ℝ)⁻¹ * ∑ k, (∑ i, φ (x i) (y (τ k i)) - φ (x k) (y k)) := by
    calc ∑ i, ∑ j, D i j * φ (x i) (y j)
        = ∑ i, ∑ j, ∑ k, (n : ℝ)⁻¹ * (((if τ k i = j then (1 : ℝ) else 0)
            - (if i = k ∧ j = k then 1 else 0)) * φ (x i) (y j)) := by
          simp only [D, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      _ = ∑ i, ∑ k, ∑ j, (n : ℝ)⁻¹ * (((if τ k i = j then (1 : ℝ) else 0)
            - (if i = k ∧ j = k then 1 else 0)) * φ (x i) (y j)) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, (n : ℝ)⁻¹ * (((if τ k i = j then (1 : ℝ) else 0)
            - (if i = k ∧ j = k then 1 else 0)) * φ (x i) (y j)) := Finset.sum_comm
      _ = ∑ k, (n : ℝ)⁻¹ * (∑ i, φ (x i) (y (τ k i)) - φ (x k) (y k)) :=
          Finset.sum_congr rfl fun k _ => by simp only [← Finset.mul_sum]; rw [hk k]
      _ = _ := by rw [Finset.mul_sum]
  rw [hcomp, inv_mul_le_iff₀ hnpos] at hL
  rw [Finset.sum_congr rfl fun k _ => key k]
  exact hL

end SoarMonoAux

open MeasureTheory in
theorem solution {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (C : ℝ) (hC : SoarBounded φ C)
    (n : ℕ) (hn : 1 ≤ n) :
    SoarHindsight P Q φ n ≤ SoarHindsight P Q φ (n + 1) := by
  have hprob : ∀ m : ℕ, IsProbabilityMeasure (SoarPairMeasure P Q m) := by
    intro m; unfold SoarPairMeasure; infer_instance
  have hmp : ∀ k : Fin (n + 1), MeasurePreserving
      (fun p : (Fin (n + 1) → X) × (Fin (n + 1) → Y) =>
        ((fun j => p.1 (k.succAbove j)), (fun j => p.2 (k.succAbove j))))
      (SoarPairMeasure P Q (n + 1)) (SoarPairMeasure P Q n) :=
    fun k => (SoarMonoAux.remove_mp P k).prod (SoarMonoAux.remove_mp Q k)
  have hA : ∀ k : Fin (n + 1),
      ∫ p, SoarHindsightSum φ (fun j => p.1 (k.succAbove j)) (fun j => p.2 (k.succAbove j))
        ∂SoarPairMeasure P Q (n + 1)
      = ∫ p, SoarHindsightSum φ p.1 p.2 ∂SoarPairMeasure P Q n := by
    intro k
    rw [← (hmp k).map_eq, integral_map (hmp k).measurable.aemeasurable
      (SoarMonoAux.meas_F φ hφ n).aestronglyMeasurable]
  have hInt : ∀ k : Fin (n + 1), Integrable
      (fun p : (Fin (n + 1) → X) × (Fin (n + 1) → Y) =>
        SoarHindsightSum φ (fun j => p.1 (k.succAbove j)) (fun j => p.2 (k.succAbove j)))
      (SoarPairMeasure P Q (n + 1)) := by
    intro k
    exact Integrable.of_bound ((SoarMonoAux.meas_F φ hφ n).comp (hmp k).measurable).aestronglyMeasurable
      (n * C) (Filter.Eventually.of_forall fun p => by
        simpa [Real.norm_eq_abs] using SoarMonoAux.bound_F φ C hC
          (fun j => p.1 (k.succAbove j)) (fun j => p.2 (k.succAbove j)))
  have hsum : ((n : ℝ) + 1) * ∫ p, SoarHindsightSum φ p.1 p.2 ∂SoarPairMeasure P Q n
      = ∫ p, ∑ k : Fin (n + 1), SoarHindsightSum φ (fun j => p.1 (k.succAbove j))
          (fun j => p.2 (k.succAbove j)) ∂SoarPairMeasure P Q (n + 1) := by
    rw [integral_finsetSum _ (fun k _ => hInt k)]
    simp only [hA, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hle : ∫ p, ∑ k : Fin (n + 1), SoarHindsightSum φ (fun j => p.1 (k.succAbove j))
          (fun j => p.2 (k.succAbove j)) ∂SoarPairMeasure P Q (n + 1)
      ≤ ∫ p, (n : ℝ) * SoarHindsightSum φ p.1 p.2 ∂SoarPairMeasure P Q (n + 1) :=
    integral_mono (integrable_finsetSum _ fun k _ => hInt k)
      ((SoarMonoAux.integrable_F φ hφ C hC (n + 1)).const_mul _)
      (fun p => SoarMonoAux.core φ hn p.1 p.2)
  rw [integral_const_mul] at hle
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  unfold SoarHindsight
  rw [div_le_div_iff₀ hnpos (by positivity)]
  push_cast
  nlinarith [hsum, hle]
