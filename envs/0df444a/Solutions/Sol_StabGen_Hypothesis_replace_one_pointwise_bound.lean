-- Prove2me | solution 1 for StabGen.Hypothesis.replace_one_pointwise_bound
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T23:19:30.427986+00:00
-- url     : https://prove2.me/submissions/4be2d551-1a54-4838-bad5-4195904b4ebe

import Init
import Mathlib
import Definitions.Def_StabGen_Hypothesis_Setting
import Definitions.Def_StabGen_Hypothesis_Stability

open MeasureTheory
namespace StabMoments
open StabGen.Hypothesis

lemma training_permutation {Z : Type*} {m : ℕ} (S : Fin m → Z)
    (e : Equiv.Perm (Fin m)) : trainingSet (S ∘ e) = trainingSet S := by
  unfold trainingSet
  rw [← Multiset.map_map]
  have h : Finset.univ.val.map e = (Finset.univ : Finset (Fin m)).val := by
    exact Multiset.map_univ_val_equiv e
  rw [h]

lemma integral_permutation {Z : Type*} [MeasurableSpace Z] (D : Measure Z)
    [IsProbabilityMeasure D] {m : ℕ} (e : Equiv.Perm (Fin m))
    (f : (Fin m → Z) → ℝ) :
    (∫ S, f (S ∘ e) ∂(Measure.pi fun _ : Fin m => D)) =
      ∫ S, f S ∂(Measure.pi fun _ : Fin m => D) := by
  have h := (measurePreserving_piCongrLeft (fun _ : Fin m => D) e.symm).integral_comp' f
  simpa [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft', Function.comp_def] using h

lemma pair_permutation {m : ℕ} (i j k l : Fin m) (hij : i ≠ j) (hkl : k ≠ l) :
    ∃ e : Equiv.Perm (Fin m), e i = k ∧ e j = l := by
  let e₁ := Equiv.swap i k
  have hi : e₁ i = k := by simp [e₁]
  have hj : e₁ j ≠ k := by rw [← hi]; exact e₁.injective.ne hij.symm
  refine ⟨e₁.trans (Equiv.swap (e₁ j) l), ?_, ?_⟩
  · simpa [Equiv.trans_apply, hi] using Equiv.swap_apply_of_ne_of_ne hj.symm hkl
  · simp

lemma diagonal_invariant {Z : Type*} [MeasurableSpace Z] (D : Measure Z)
    [IsProbabilityMeasure D] {m : ℕ} (f : Multiset Z → Z → ℝ) (i k : Fin m)
    (g : ℝ → ℝ) :
    (∫ S, g (f (trainingSet S) (S i)) ∂(Measure.pi fun _ : Fin m => D)) =
      ∫ S, g (f (trainingSet S) (S k)) ∂(Measure.pi fun _ : Fin m => D) := by
  have h := integral_permutation D (Equiv.swap i k)
    (fun S => g (f (trainingSet S) (S i)))
  simpa only [training_permutation, Function.comp_apply, Equiv.swap_apply_left] using h.symm

lemma pair_invariant {Z : Type*} [MeasurableSpace Z] (D : Measure Z)
    [IsProbabilityMeasure D] {m : ℕ} (f : Multiset Z → Z → ℝ)
    (i j k l : Fin m) (hij : i ≠ j) (hkl : k ≠ l) :
    (∫ S, f (trainingSet S) (S i) * f (trainingSet S) (S j)
      ∂(Measure.pi fun _ : Fin m => D)) =
    ∫ S, f (trainingSet S) (S k) * f (trainingSet S) (S l)
      ∂(Measure.pi fun _ : Fin m => D) := by
  obtain ⟨e, he, he'⟩ := pair_permutation i j k l hij hkl
  have h := integral_permutation D e
    (fun S => f (trainingSet S) (S i) * f (trainingSet S) (S j))
  simpa only [training_permutation, Function.comp_apply, he, he'] using h.symm

lemma mixed_invariant {Z : Type*} [MeasurableSpace Z] (D : Measure Z)
    [IsProbabilityMeasure D] {m : ℕ} (f : Multiset Z → Z → ℝ)
    (r : Multiset Z → ℝ) (i k : Fin m) :
    (∫ S, r (trainingSet S) * f (trainingSet S) (S i)
      ∂(Measure.pi fun _ : Fin m => D)) =
    ∫ S, r (trainingSet S) * f (trainingSet S) (S k)
      ∂(Measure.pi fun _ : Fin m => D) := by
  have h := integral_permutation D (Equiv.swap i k)
    (fun S => r (trainingSet S) * f (trainingSet S) (S i))
  simpa only [training_permutation, Function.comp_apply, Equiv.swap_apply_left] using h.symm
end StabMoments

open MeasureTheory
namespace StabMoments
open StabGen.Hypothesis

lemma bounded_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {g : Ω → ℝ} (hg : Measurable g) (C : ℝ)
    (hb : ∀ x, |g x| ≤ C) : Integrable g μ :=
  (integrable_const C).mono' hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)

lemma bounded_product {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {g h : Ω → ℝ} (hg : Measurable g) (hh : Measurable h)
    (C : ℝ) (bg : ∀ x, |g x| ≤ C) (bh : ∀ x, |h x| ≤ C) :
    Integrable (fun x => g x * h x) μ := by
  apply bounded_integrable μ (hg.mul hh) (C*C)
  intro x
  change |g x * h x| ≤ C * C
  rw [abs_mul]
  exact mul_le_mul (bg x) (bh x) (abs_nonneg _) (le_trans (abs_nonneg _) (bg x))

variable {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    {m : ℕ} (f : Multiset Z → Z → ℝ)
    (hf : Measurable (fun p : (Fin m → Z) × Z => f (trainingSet p.1) p.2))
    (M : ℝ) (hb : ∀ T z, 0 ≤ f T z ∧ f T z ≤ M)

include hf in
lemma loss_measurable (i : Fin m) : Measurable (fun S : Fin m → Z => f (trainingSet S) (S i)) :=
  hf.comp (measurable_id.prodMk (measurable_pi_apply i))

include hb in
lemma loss_bound (S : Fin m → Z) (i : Fin m) :
    |f (trainingSet S) (S i)| ≤ |M| := by
  rw [abs_of_nonneg (hb _ _).1]
  exact (hb _ _).2.trans (le_abs_self M)

include hf hb in
lemma loss_integrable (i : Fin m) :
    Integrable (fun S : Fin m → Z => f (trainingSet S) (S i)) (Measure.pi fun _ => D) :=
  bounded_integrable _ (loss_measurable f hf i) |M| (fun S => loss_bound f M hb S i)

include hf hb in
lemma loss_product_integrable (i j : Fin m) :
    Integrable (fun S : Fin m → Z => f (trainingSet S) (S i) * f (trainingSet S) (S j))
      (Measure.pi fun _ => D) :=
  bounded_product _ (loss_measurable f hf i) (loss_measurable f hf j) |M|
    (fun S => loss_bound f M hb S i) (fun S => loss_bound f M hb S j)

include hf hb in
lemma fresh_integrable (S : Fin m → Z) : Integrable (f (trainingSet S)) D := by
  apply bounded_integrable D (hf.comp (measurable_const.prodMk measurable_id)) |M|
  intro z
  change |f (trainingSet S) z| ≤ |M|
  rw [abs_of_nonneg (hb _ _).1]
  exact (hb _ _).2.trans (le_abs_self M)

include hf in
lemma risk_measurable : Measurable (fun S : Fin m → Z => ∫ z, f (trainingSet S) z ∂D) :=
  hf.stronglyMeasurable.integral_prod_right'.measurable

include hf hb in
include hf hb in
lemma risk_bounds (S : Fin m → Z) :
    0 ≤ (∫ z, f (trainingSet S) z ∂D) ∧ (∫ z, f (trainingSet S) z ∂D) ≤ M := by
  refine ⟨integral_nonneg fun z => (hb _ _).1, ?_⟩
  calc
    _ ≤ ∫ _ : Z, M ∂D := integral_mono (fresh_integrable D f hf M hb S)
      (integrable_const M) (fun z => (hb _ _).2)
    _ = M := by simp

include hf hb in
lemma risk_bound (S : Fin m → Z) : |∫ z, f (trainingSet S) z ∂D| ≤ |M| := by
  rw [abs_of_nonneg (risk_bounds D f hf M hb S).1]
  exact (risk_bounds D f hf M hb S).2.trans (le_abs_self M)

include hf hb in
lemma mixed_integrable (i : Fin m) :
    Integrable (fun S : Fin m → Z => (∫ z, f (trainingSet S) z ∂D) * f (trainingSet S) (S i))
      (Measure.pi fun _ => D) :=
  bounded_product _ (risk_measurable D f hf) (loss_measurable f hf i) |M|
    (risk_bound D f hf M hb) (fun S => loss_bound f M hb S i)
end StabMoments

open MeasureTheory
namespace LooMoments
open StabGen.Hypothesis StabMoments

lemma training_cons_remove {Z : Type*} {m : ℕ} (S : Fin m → Z) (i : Fin m) :
    trainingSet S = S i ::ₘ removeAt S i := by
  classical
  unfold trainingSet removeAt
  change Finset.univ.val.map S = S i ::ₘ (Finset.univ.val.erase i).map S
  rw [← Multiset.map_cons, Multiset.cons_erase (by simp)]

lemma remove_permutation {Z : Type*} {m : ℕ} (S : Fin m → Z)
    (e : Equiv.Perm (Fin m)) (i : Fin m) :
    removeAt (S ∘ e) i = removeAt S (e i) := by
  have h := (training_cons_remove (S ∘ e) i).symm.trans
    ((training_permutation S e).trans (training_cons_remove S (e i)))
  exact (Multiset.cons_inj_right (S (e i))).1 h

lemma remove_representation {Z : Type*} {m : ℕ} (S : Fin (m+1) → Z) (i : Fin (m+1)) :
    removeAt S i = trainingSet (S ∘ i.succAbove) := by
  unfold removeAt trainingSet
  rw [Fin.univ_succAbove m i]
  simp [Finset.map_val, Function.comp_def]

variable {Z : Type*} [MeasurableSpace Z] (f : Multiset Z → Z → ℝ)
    (hf : ∀ n, Measurable (fun p : (Fin n → Z) × Z => f (trainingSet p.1) p.2))

include hf in
lemma removed_measurable {m : ℕ} (i : Fin m) :
    Measurable (fun p : (Fin m → Z) × Z => f (removeAt p.1 i) p.2) := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ n =>
    simp_rw [remove_representation]
    have hg : Measurable (fun p : (Fin (n+1) → Z) × Z => (p.1 ∘ i.succAbove, p.2)) := by fun_prop
    exact (hf n).comp hg

include hf in
lemma loss_measurable {m : ℕ} (i : Fin m) :
    Measurable (fun S : Fin m → Z => f (removeAt S i) (S i)) :=
  (removed_measurable f hf i).comp (measurable_id.prodMk (measurable_pi_apply i))

lemma diagonal_invariant {m : ℕ} (D : Measure Z) [IsProbabilityMeasure D]
    (i k : Fin m) (g : ℝ → ℝ) :
    (∫ S, g (f (removeAt S i) (S i)) ∂(Measure.pi fun _ : Fin m => D)) =
      ∫ S, g (f (removeAt S k) (S k)) ∂(Measure.pi fun _ : Fin m => D) := by
  have h := integral_permutation D (Equiv.swap i k)
    (fun S => g (f (removeAt S i) (S i)))
  simpa only [remove_permutation, Function.comp_apply, Equiv.swap_apply_left] using h.symm

lemma pair_invariant {m : ℕ} (D : Measure Z) [IsProbabilityMeasure D]
    (i j k l : Fin m) (hij : i ≠ j) (hkl : k ≠ l) :
    (∫ S, f (removeAt S i) (S i) * f (removeAt S j) (S j)
      ∂(Measure.pi fun _ : Fin m => D)) =
    ∫ S, f (removeAt S k) (S k) * f (removeAt S l) (S l)
      ∂(Measure.pi fun _ : Fin m => D) := by
  obtain ⟨e, he, he'⟩ := pair_permutation i j k l hij hkl
  have h := integral_permutation D e
    (fun S => f (removeAt S i) (S i) * f (removeAt S j) (S j))
  simpa only [remove_permutation, Function.comp_apply, he, he'] using h.symm

lemma mixed_invariant {m : ℕ} (D : Measure Z) [IsProbabilityMeasure D]
    (r : Multiset Z → ℝ) (i k : Fin m) :
    (∫ S, r (trainingSet S) * f (removeAt S i) (S i)
      ∂(Measure.pi fun _ : Fin m => D)) =
    ∫ S, r (trainingSet S) * f (removeAt S k) (S k)
      ∂(Measure.pi fun _ : Fin m => D) := by
  have h := integral_permutation D (Equiv.swap i k)
    (fun S => r (trainingSet S) * f (removeAt S i) (S i))
  simpa only [training_permutation, remove_permutation, Function.comp_apply,
    Equiv.swap_apply_left] using h.symm
end LooMoments

open MeasureTheory
namespace ReplaceStability
open StabGen.Hypothesis
lemma remove_replace {Z : Type*} {m : ℕ} (S : Fin m → Z) (i : Fin m) (z : Z) :
    removeAt (replaceAt S i z) i = removeAt S i := by
  classical
  unfold removeAt replaceAt
  apply Multiset.map_congr rfl
  intro j hj
  change j ∈ (Finset.univ.erase i : Finset (Fin m)) at hj
  exact Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
lemma swapped_pack {Z : Type*} {m : ℕ} (S : Fin (m+1) → Z) (i : Fin m) :
    (Fin.init (α := fun _ => Z) (S ∘ Equiv.swap i.castSucc (Fin.last m)),
      (S ∘ Equiv.swap i.castSucc (Fin.last m)) (Fin.last m)) =
      (replaceAt (Fin.init S) i (S (Fin.last m)), (Fin.init S) i) := by
  classical
  apply Prod.ext
  · funext j
    by_cases h : j = i
    · subst j
      simp [Fin.init_def,replaceAt,Function.comp_def]
    · have hj : j.castSucc ≠ i.castSucc := by simpa using h
      simp [Fin.init_def,replaceAt,Function.comp_def,Function.update_of_ne h,
        Equiv.swap_apply_of_ne_of_ne hj (Fin.castSucc_ne_last j)]
  · simp [Fin.init_def,Function.comp_def]
lemma augmented_integral {Z : Type*} [MeasurableSpace Z] (D : Measure Z)
    [IsProbabilityMeasure D] {m : ℕ} (f : (Fin m → Z) × Z → ℝ) :
    (∫ S, f (Fin.init (α := fun _ => Z) S,S (Fin.last m))
      ∂(Measure.pi fun _ : Fin (m+1) => D)) =
      ∫ p, f p ∂((Measure.pi fun _ : Fin m => D).prod D) := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => D) (Fin.last m)).integral_comp'
    (fun p : Z × (Fin m → Z) => f (p.2,p.1))
  change (∫ S, f (S ∘ (Fin.last m).succAbove,S (Fin.last m))
      ∂(Measure.pi fun _ : Fin (m+1) => D)) =
      ∫ p : Z × (Fin m → Z), f (p.2,p.1) ∂(D.prod (Measure.pi fun _ : Fin m => D)) at hp
  simp_rw [Fin.succAbove_last] at hp
  change (∫ S, f (Fin.init (α := fun _ => Z) S,S (Fin.last m))
      ∂(Measure.pi fun _ : Fin (m+1) => D)) = _ at hp
  exact hp.trans (integral_prod_swap f)
lemma exchange_integral {Z : Type*} [MeasurableSpace Z] (D : Measure Z)
    [IsProbabilityMeasure D] {m : ℕ} (i : Fin m) (f : (Fin m → Z) × Z → ℝ) :
    (∫ p, f (replaceAt p.1 i p.2,p.1 i) ∂((Measure.pi fun _ : Fin m => D).prod D)) =
      ∫ p, f p ∂((Measure.pi fun _ : Fin m => D).prod D) := by
  rw [← augmented_integral D (fun p => f (replaceAt p.1 i p.2,p.1 i)),
    ← augmented_integral D f]
  have h := StabMoments.integral_permutation D (Equiv.swap i.castSucc (Fin.last m))
    (fun S => f (Fin.init (α := fun _ => Z) S,S (Fin.last m)))
  simpa only [swapped_pack] using h
end ReplaceStability

open MeasureTheory
namespace ReplaceStability
open StabGen.Hypothesis
lemma replaced_measurable {Z : Type*} [MeasurableSpace Z] {m : ℕ} (i : Fin m) :
    Measurable (fun p : (Fin m → Z) × Z => replaceAt p.1 i p.2) := by
  apply measurable_pi_lambda
  intro j
  by_cases h : j = i
  · subst j
    simpa [replaceAt] using (measurable_snd : Measurable (fun p : (Fin m → Z) × Z => p.2))
  · simpa [replaceAt,Function.update_of_ne h,Function.comp_def] using
      ((measurable_pi_apply j).comp measurable_fst : Measurable (fun p : (Fin m → Z) × Z => p.1 j))
lemma replace_bound {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (f : Multiset Z → Z → ℝ)
    (hf : ∀ n, Measurable (fun p : (Fin n → Z) × Z => f (trainingSet p.1) p.2))
    (M : ℝ) (hb : ∀ T z, 0 ≤ f T z ∧ f T z ≤ M)
    {m : ℕ} (i : Fin m) (β₁ β₂ : ℝ)
    (h₁ : (∫ p : (Fin m → Z) × Z, |f (trainingSet p.1) p.2 - f (removeAt p.1 i) p.2|
      ∂((Measure.pi fun _ : Fin m => D).prod D)) ≤ β₁)
    (h₂ : (∫ S : Fin m → Z, |f (trainingSet S) (S i) - f (removeAt S i) (S i)|
      ∂(Measure.pi fun _ : Fin m => D)) ≤ β₂) :
    (∫ p : (Fin m → Z) × Z, |f (trainingSet p.1) (p.1 i) -
      f (trainingSet (replaceAt p.1 i p.2)) (p.1 i)|
      ∂((Measure.pi fun _ : Fin m => D).prod D)) ≤ β₁ + β₂ := by
  let μ := (Measure.pi fun _ : Fin m => D).prod D
  have hb' (T : Multiset Z) (z : Z) : |f T z| ≤ |M| := by
    rw [abs_of_nonneg (hb _ _).1]
    exact (hb _ _).2.trans (le_abs_self M)
  have hfull : Measurable (fun p : (Fin m → Z) × Z => f (trainingSet p.1) (p.1 i)) :=
    (hf m).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_fst))
  have hdel : Measurable (fun p : (Fin m → Z) × Z => f (removeAt p.1 i) (p.1 i)) :=
    (LooMoments.removed_measurable f hf i).comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_fst))
  have hrep : Measurable (fun p : (Fin m → Z) × Z => f (trainingSet (replaceAt p.1 i p.2)) (p.1 i)) :=
    (hf m).comp ((replaced_measurable i).prodMk ((measurable_pi_apply i).comp measurable_fst))
  have ifull := StabMoments.bounded_integrable μ hfull |M| (fun p => hb' _ _)
  have idel := StabMoments.bounded_integrable μ hdel |M| (fun p => hb' _ _)
  have irep := StabMoments.bounded_integrable μ hrep |M| (fun p => hb' _ _)
  have first : (∫ p : (Fin m → Z) × Z, |f (trainingSet p.1) (p.1 i) - f (removeAt p.1 i) (p.1 i)| ∂μ) ≤ β₂ := by
    calc
      _ = ∫ S : Fin m → Z, (∫ _ : Z, |f (trainingSet S) (S i) - f (removeAt S i) (S i)| ∂D)
          ∂(Measure.pi fun _ : Fin m => D) :=
        integral_prod (fun p : (Fin m → Z) × Z => |f (trainingSet p.1) (p.1 i) - f (removeAt p.1 i) (p.1 i)|)
          (ifull.sub idel).abs
      _ ≤ β₂ := by simpa using h₂
  have second : (∫ p : (Fin m → Z) × Z, |f (removeAt p.1 i) (p.1 i) -
      f (trainingSet (replaceAt p.1 i p.2)) (p.1 i)| ∂μ) ≤ β₁ := by
    have hx := exchange_integral D i (fun p : (Fin m → Z) × Z =>
      |f (trainingSet p.1) p.2 - f (removeAt p.1 i) p.2|)
    simp only [remove_replace] at hx
    calc
      _ = ∫ p : (Fin m → Z) × Z, |f (trainingSet (replaceAt p.1 i p.2)) (p.1 i) -
          f (removeAt p.1 i) (p.1 i)| ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with p
        exact abs_sub_comm _ _
      _ = _ := hx
      _ ≤ β₁ := h₁
  calc
    _ ≤ ∫ p : (Fin m → Z) × Z,
      (|f (trainingSet p.1) (p.1 i) - f (removeAt p.1 i) (p.1 i)| +
      |f (removeAt p.1 i) (p.1 i) - f (trainingSet (replaceAt p.1 i p.2)) (p.1 i)|) ∂μ :=
      integral_mono (ifull.sub irep).abs ((ifull.sub idel).abs.add (idel.sub irep).abs)
        (fun p => abs_sub_le _ _ _)
    _ = _ := integral_add (ifull.sub idel).abs (idel.sub irep).abs
    _ ≤ β₂ + β₁ := add_le_add first second
    _ = β₁ + β₂ := add_comm _ _
end ReplaceStability

open MeasureTheory StabGen.Hypothesis FoundationsML.Stability
theorem solution {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ) (M : ℝ)
    (hL : ∀ (y' : Y') (y : Y), 0 ≤ L y' y ∧ L y' y ≤ M)
    (A : LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable (fun p : (Fin n → X × Y) × (X × Y) =>
      Loss L (A (trainingSet p.1)) p.2))
    (m : ℕ) (β₁ β₂ : ℝ) (h₁ : HypothesisStable D L A m β₁)
    (h₂ : PointwiseHypothesisStable D L A m β₂) (i : Fin m) :
    ∫ p : (Fin m → X × Y) × (X × Y),
        |Loss L (A (trainingSet p.1)) (p.1 i)
          - Loss L (A (trainingSet (replaceAt p.1 i p.2))) (p.1 i)|
      ∂((Measure.pi fun _ : Fin m => D).prod D)
    ≤ β₁ + β₂ := by
  exact ReplaceStability.replace_bound D (fun T z => Loss L (A T) z) hA M
    (fun T z => hL _ _) i β₁ β₂ (h₁ i).2 (h₂ i).2
#print axioms solution
