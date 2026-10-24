-- Prove2me | solution 1 for StabGen.Hypothesis.lemma25_loo
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T22:25:12.930433+00:00
-- url     : https://prove2.me/submissions/ccfd8fd8-96a1-4766-a473-0f0caf0120f4

import Init
import Mathlib
import Definitions.Def_StabGen_Hypothesis_Setting
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError

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
namespace LooMoments
open StabGen.Hypothesis
variable {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    {m : ℕ} (f : Multiset Z → Z → ℝ)
    (hf : ∀ n, Measurable (fun p : (Fin n → Z) × Z => f (trainingSet p.1) p.2))
    (M : ℝ) (hb : ∀ T z, 0 ≤ f T z ∧ f T z ≤ M)

include hb in
lemma loss_bound (S : Fin m → Z) (i : Fin m) : |f (removeAt S i) (S i)| ≤ |M| := by
  rw [abs_of_nonneg (hb _ _).1]
  exact (hb _ _).2.trans (le_abs_self M)

include hf hb in
lemma loss_integrable (i : Fin m) :
    Integrable (fun S : Fin m → Z => f (removeAt S i) (S i)) (Measure.pi fun _ => D) :=
  StabMoments.bounded_integrable _ (loss_measurable f hf i) |M| (fun S => loss_bound f M hb S i)

include hf hb in
lemma loss_product_integrable (i j : Fin m) :
    Integrable (fun S : Fin m → Z => f (removeAt S i) (S i) * f (removeAt S j) (S j))
      (Measure.pi fun _ => D) :=
  StabMoments.bounded_product _ (loss_measurable f hf i) (loss_measurable f hf j) |M|
    (fun S => loss_bound f M hb S i) (fun S => loss_bound f M hb S j)

include hf hb in
lemma mixed_integrable (i : Fin m) :
    Integrable (fun S : Fin m → Z => (∫ z, f (trainingSet S) z ∂D) * f (removeAt S i) (S i))
      (Measure.pi fun _ => D) :=
  StabMoments.bounded_product _ (StabMoments.risk_measurable D f (hf m))
    (loss_measurable f hf i) |M| (StabMoments.risk_bound D f (hf m) M hb)
    (fun S => loss_bound f M hb S i)

include hf hb in
lemma fresh_mixed (i : Fin m) :
    (∫ p : (Fin m → Z) × Z, f (trainingSet p.1) p.2 * f (removeAt p.1 i) (p.1 i)
      ∂((Measure.pi fun _ : Fin m => D).prod D)) =
    ∫ S, (∫ z, f (trainingSet S) z ∂D) * f (removeAt S i) (S i)
      ∂(Measure.pi fun _ : Fin m => D) := by
  have hi : Integrable (fun p : (Fin m → Z) × Z =>
      f (trainingSet p.1) p.2 * f (removeAt p.1 i) (p.1 i))
      ((Measure.pi fun _ : Fin m => D).prod D) := by
    apply StabMoments.bounded_product _ (hf m) ((loss_measurable f hf i).comp measurable_fst) |M|
    · intro p
      rw [abs_of_nonneg (hb _ _).1]
      exact (hb _ _).2.trans (le_abs_self M)
    · intro p
      exact loss_bound f M hb p.1 i
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with S
  exact integral_mul_const _ _
end LooMoments

open MeasureTheory
open scoped BigOperators
namespace LooMoments
open StabGen.Hypothesis
noncomputable def emp {Z : Type*} {m : ℕ} (f : Multiset Z → Z → ℝ) (S : Fin m → Z) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, f (removeAt S i) (S i)

lemma sum_diagonal {m : ℕ} (k : Fin m) (a b : ℝ) :
    (∑ l : Fin m, if k = l then a else b) = a + ((m : ℝ)-1)*b := by
  calc
    _ = ∑ l : Fin m, (b + if k = l then a-b else 0) := by
      apply Finset.sum_congr rfl
      intro l _
      split_ifs <;> ring
    _ = a + ((m : ℝ)-1)*b := by simp [Finset.sum_add_distrib]; ring

variable {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    {m : ℕ} (f : Multiset Z → Z → ℝ)
    (hf : ∀ n, Measurable (fun p : (Fin n → Z) × Z => f (trainingSet p.1) p.2))
    (M : ℝ) (hb : ∀ T z, 0 ≤ f T z ∧ f T z ≤ M)
include hf hb

lemma empirical_second_moment (hm : 0 < m) (i j : Fin m) (hij : i ≠ j) :
    (∫ S, (emp f S)^2 ∂(Measure.pi fun _ : Fin m => D)) =
      (1 / (m : ℝ)) * (∫ S, (f (removeAt S i) (S i))^2 ∂(Measure.pi fun _ : Fin m => D)) +
      (((m : ℝ)-1) / (m : ℝ)) *
        (∫ S, f (removeAt S i) (S i) * f (removeAt S j) (S j)
          ∂(Measure.pi fun _ : Fin m => D)) := by
  let μ := Measure.pi (fun _ : Fin m => D)
  let a := ∫ S, (f (removeAt S i) (S i))^2 ∂μ
  let b := ∫ S, f (removeAt S i) (S i) * f (removeAt S j) (S j) ∂μ
  have hpair (k l : Fin m) :
      (∫ S, f (removeAt S k) (S k) * f (removeAt S l) (S l) ∂μ) =
      if k = l then a else b := by
    by_cases h : k = l
    · subst l
      simpa [a, μ, pow_two] using diagonal_invariant f D k i (fun x => x*x)
    · simpa only [if_neg h, b] using pair_invariant f D k l i j h hij
  have hpoint (S : Fin m → Z) : (emp f S)^2 =
      (1 / (m : ℝ))^2 * ∑ k, ∑ l, f (removeAt S k) (S k) * f (removeAt S l) (S l) := by
    unfold emp
    rw [mul_pow, pow_two (∑ k, f (removeAt S k) (S k)), Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  have hmi : (m : ℝ) ≠ 0 := by positivity
  calc
    _ = (1 / (m : ℝ))^2 * ∫ S, ∑ k, ∑ l,
        f (removeAt S k) (S k) * f (removeAt S l) (S l) ∂μ := by
      simp_rw [hpoint]
      exact integral_const_mul _ _
    _ = (1 / (m : ℝ))^2 * ∑ k, ∑ l,
        ∫ S, f (removeAt S k) (S k) * f (removeAt S l) (S l) ∂μ := by
      congr 1
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro k _
        exact integral_finsetSum _ (fun l _ => loss_product_integrable D f hf M hb k l)
      · intro k _
        exact integrable_finsetSum _ (fun l _ => loss_product_integrable D f hf M hb k l)
    _ = (1 / (m : ℝ))^2 * ((m : ℝ)*(a + ((m : ℝ)-1)*b)) := by
      simp_rw [hpair, sum_diagonal]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = _ := by change _ = (1/(m:ℝ))*a + (((m:ℝ)-1)/(m:ℝ))*b; field_simp

lemma empirical_second_moment_bound (hm : 0 < m) (i j : Fin m) (hij : i ≠ j) :
    (∫ S, (emp f S)^2 ∂(Measure.pi fun _ : Fin m => D)) ≤
      M / (m : ℝ) * (∫ S, f (removeAt S i) (S i) ∂(Measure.pi fun _ : Fin m => D)) +
      (((m : ℝ)-1) / (m : ℝ)) *
        (∫ S, f (removeAt S i) (S i) * f (removeAt S j) (S j)
          ∂(Measure.pi fun _ : Fin m => D)) := by
  rw [empirical_second_moment D f hf M hb hm i j hij]
  have h : (∫ S, (f (removeAt S i) (S i))^2 ∂(Measure.pi fun _ : Fin m => D)) ≤
      M * ∫ S, f (removeAt S i) (S i) ∂(Measure.pi fun _ : Fin m => D) := by
    rw [← integral_const_mul]
    apply integral_mono
    · simpa only [pow_two] using loss_product_integrable D f hf M hb i i
    · exact (loss_integrable D f hf M hb i).const_mul M
    · intro S
      have h := hb (removeAt S i) (S i)
      nlinarith [mul_nonneg h.1 (sub_nonneg.mpr h.2)]
  have := mul_le_mul_of_nonneg_left h (show 0 ≤ 1/(m:ℝ) by positivity)
  apply add_le_add _ le_rfl
  convert this using 1 <;> ring

lemma mixed_empirical (hm : 0 < m) (i : Fin m) :
    (∫ S, (∫ z, f (trainingSet S) z ∂D) * emp f S ∂(Measure.pi fun _ : Fin m => D)) =
    ∫ S, (∫ z, f (trainingSet S) z ∂D) * f (removeAt S i) (S i)
      ∂(Measure.pi fun _ : Fin m => D) := by
  have hpoint (S : Fin m → Z) :
      (∫ z, f (trainingSet S) z ∂D) * emp f S =
      (1/(m:ℝ)) * ∑ k, (∫ z, f (trainingSet S) z ∂D) * f (removeAt S k) (S k) := by
    simp only [emp, ← Finset.mul_sum]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul, integral_finsetSum _ (fun k _ => mixed_integrable D f hf M hb k)]
  have heq (k : Fin m) := mixed_invariant f D (fun T => ∫ z, f T z ∂D) k i
  simp_rw [heq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hm' : (m:ℝ) ≠ 0 := by positivity
  field_simp
end LooMoments

open MeasureTheory
namespace StabMoments
open StabGen.Hypothesis
variable {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    {m : ℕ} (f : Multiset Z → Z → ℝ)
    (hf : Measurable (fun p : (Fin m → Z) × Z => f (trainingSet p.1) p.2))
    (M : ℝ) (hb : ∀ T z, 0 ≤ f T z ∧ f T z ≤ M)
include hf hb

lemma fresh_bound (T : Multiset Z) (z : Z) : |f T z| ≤ |M| := by
  rw [abs_of_nonneg (hb _ _).1]
  exact (hb _ _).2.trans (le_abs_self M)

lemma fresh_mixed (i : Fin m) :
    (∫ p : (Fin m → Z) × Z, f (trainingSet p.1) p.2 * f (trainingSet p.1) (p.1 i)
      ∂((Measure.pi fun _ : Fin m => D).prod D)) =
    ∫ S, (∫ z, f (trainingSet S) z ∂D) * f (trainingSet S) (S i)
      ∂(Measure.pi fun _ : Fin m => D) := by
  have hi : Integrable (fun p : (Fin m → Z) × Z =>
      f (trainingSet p.1) p.2 * f (trainingSet p.1) (p.1 i))
      ((Measure.pi fun _ : Fin m => D).prod D) :=
    bounded_product _ hf ((loss_measurable f hf i).comp measurable_fst) |M|
      (fun p => fresh_bound f hf M hb _ _) (fun p => fresh_bound f hf M hb _ _)
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with S
  exact integral_mul_const _ _

lemma fresh_square :
    (∫ p : ((Fin m → Z) × Z) × Z,
        f (trainingSet p.1.1) p.1.2 * f (trainingSet p.1.1) p.2
      ∂(((Measure.pi fun _ : Fin m => D).prod D).prod D)) =
    ∫ S, (∫ z, f (trainingSet S) z ∂D)^2 ∂(Measure.pi fun _ : Fin m => D) := by
  have hi : Integrable (fun p : ((Fin m → Z) × Z) × Z =>
        f (trainingSet p.1.1) p.1.2 * f (trainingSet p.1.1) p.2)
      (((Measure.pi fun _ : Fin m => D).prod D).prod D) :=
    bounded_product _ (hf.comp measurable_fst)
      (hf.comp ((measurable_fst.fst).prodMk measurable_snd)) |M|
      (fun p => fresh_bound f hf M hb _ _) (fun p => fresh_bound f hf M hb _ _)
  have hi' : Integrable (fun p : (Fin m → Z) × Z =>
        f (trainingSet p.1) p.2 * (∫ z, f (trainingSet p.1) z ∂D))
      ((Measure.pi fun _ : Fin m => D).prod D) :=
    bounded_product _ hf ((risk_measurable D f hf).comp measurable_fst) |M|
      (fun p => fresh_bound f hf M hb _ _) (fun p => risk_bound D f hf M hb p.1)
  rw [integral_prod _ hi]
  simp_rw [integral_const_mul]
  rw [integral_prod _ hi']
  apply integral_congr_ae
  filter_upwards [] with S
  rw [integral_mul_const, pow_two]
end StabMoments

open MeasureTheory
namespace LooMoments
open StabGen.Hypothesis

lemma heldout_expectation {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (f : Multiset Z → Z → ℝ)
    (hf : ∀ n, Measurable (fun p : (Fin n → Z) × Z => f (trainingSet p.1) p.2))
    (M : ℝ) (hb : ∀ T z, 0 ≤ f T z ∧ f T z ≤ M)
    {m : ℕ} (i : Fin m) :
    (∫ S, f (removeAt S i) (S i) ∂(Measure.pi fun _ : Fin m => D)) =
      ∫ S, (∫ z, f (removeAt S i) z ∂D) ∂(Measure.pi fun _ : Fin m => D) := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ n =>
    let μ := Measure.pi (fun _ : Fin n => D)
    have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => D) i
    have hi : Integrable (fun p : Z × (Fin n → Z) => f (trainingSet p.2) p.1) (D.prod μ) := by
      apply StabMoments.bounded_integrable _ ((hf n).comp (measurable_snd.prodMk measurable_fst)) |M|
      intro p
      change |f (trainingSet p.2) p.1| ≤ |M|
      rw [abs_of_nonneg (hb _ _).1]
      exact (hb _ _).2.trans (le_abs_self M)
    have hir : Integrable (fun p : Z × (Fin n → Z) => ∫ z, f (trainingSet p.2) z ∂D) (D.prod μ) :=
      StabMoments.bounded_integrable _ ((StabMoments.risk_measurable D f (hf n)).comp measurable_snd)
        |M| (fun p => StabMoments.risk_bound D f (hf n) M hb p.2)
    have hleft := hp.integral_comp' (fun p : Z × (Fin n → Z) => f (trainingSet p.2) p.1)
    have hright := hp.integral_comp' (fun p : Z × (Fin n → Z) => ∫ z, f (trainingSet p.2) z ∂D)
    change (∫ S, f (trainingSet (S ∘ i.succAbove)) (S i) ∂(Measure.pi fun _ : Fin (n+1) => D)) =
      (∫ p : Z × (Fin n → Z), f (trainingSet p.2) p.1 ∂(D.prod μ)) at hleft
    change (∫ S, (∫ z, f (trainingSet (S ∘ i.succAbove)) z ∂D)
      ∂(Measure.pi fun _ : Fin (n+1) => D)) =
      (∫ p : Z × (Fin n → Z), (∫ z, f (trainingSet p.2) z ∂D) ∂(D.prod μ)) at hright
    simp_rw [remove_representation]
    rw [hleft, hright, integral_prod_symm _ hi, integral_prod _ hir]
    simp
end LooMoments

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
namespace LooMoments
open StabGen.Hypothesis StabMoments
variable {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    {m : ℕ} (f : Multiset Z → Z → ℝ)
    (hf : ∀ n, Measurable (fun p : (Fin n → Z) × Z => f (trainingSet p.1) p.2))
    (M : ℝ) (hb : ∀ T z, 0 ≤ f T z ∧ f T z ≤ M)
include hf hb

lemma emp_measurable : Measurable (fun S : Fin m → Z => emp f S) := by
  unfold emp
  exact measurable_const.mul (Finset.measurable_sum _ (fun i _ => loss_measurable f hf i))

lemma emp_bound (hm : 0 < m) (S : Fin m → Z) : |emp f S| ≤ |M| := by
  have hs : |∑ i, f (removeAt S i) (S i)| ≤ (m : ℝ)*|M| := by
    calc
      _ ≤ ∑ i, |f (removeAt S i) (S i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin m, |M| := Finset.sum_le_sum (fun i _ => loss_bound f M hb S i)
      _ = _ := by simp
  have hm' : (m:ℝ) ≠ 0 := by positivity
  calc
    _ = (1/(m:ℝ))*|∑ i, f (removeAt S i) (S i)| := by
      rw [emp, abs_mul, abs_of_nonneg (show 0 ≤ 1/(m:ℝ) by positivity)]
    _ ≤ (1/(m:ℝ))*((m:ℝ)*|M|) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = |M| := by field_simp

lemma deviation_expansion (hm : 0 < m) :
    (∫ S, ((∫ z, f (trainingSet S) z ∂D) - emp f S)^2
      ∂(Measure.pi fun _ : Fin m => D)) =
    (∫ S, (∫ z, f (trainingSet S) z ∂D)^2 ∂(Measure.pi fun _ : Fin m => D)) -
      2 * (∫ S, (∫ z, f (trainingSet S) z ∂D) * emp f S
        ∂(Measure.pi fun _ : Fin m => D)) +
      (∫ S, (emp f S)^2 ∂(Measure.pi fun _ : Fin m => D)) := by
  let μ := Measure.pi (fun _ : Fin m => D)
  have hr : Integrable (fun S : Fin m → Z => (∫ z, f (trainingSet S) z ∂D)^2) μ := by
    simpa only [pow_two] using bounded_product μ (StabMoments.risk_measurable D f (hf m))
      (StabMoments.risk_measurable D f (hf m)) |M| (StabMoments.risk_bound D f (hf m) M hb) (StabMoments.risk_bound D f (hf m) M hb)
  have he : Integrable (fun S : Fin m → Z => (emp f S)^2) μ := by
    simpa only [pow_two] using bounded_product μ (emp_measurable f hf M hb)
      (emp_measurable f hf M hb) |M| (emp_bound f hf M hb hm) (emp_bound f hf M hb hm)
  have hx : Integrable (fun S : Fin m → Z => (∫ z, f (trainingSet S) z ∂D) * emp f S) μ :=
    bounded_product μ (StabMoments.risk_measurable D f (hf m)) (emp_measurable f hf M hb) |M|
      (StabMoments.risk_bound D f (hf m) M hb) (emp_bound f hf M hb hm)
  have hp (S : Fin m → Z) : ((∫ z, f (trainingSet S) z ∂D) - emp f S)^2 =
      (∫ z, f (trainingSet S) z ∂D)^2 - 2*((∫ z, f (trainingSet S) z ∂D)*emp f S) + (emp f S)^2 := by ring
  simp_rw [hp]
  have hadd := integral_add (hr.sub (hx.const_mul 2)) he
  have hsub := integral_sub hr (hx.const_mul 2)
  dsimp only [Pi.sub_apply] at hadd
  rw [hsub, integral_const_mul] at hadd
  exact hadd

lemma deviation_bound (hm : 0 < m) (i j : Fin m) (hij : i ≠ j) :
    (∫ S, ((∫ z, f (trainingSet S) z ∂D) - emp f S)^2
      ∂(Measure.pi fun _ : Fin m => D)) ≤
    (∫ p : ((Fin m → Z) × Z) × Z,
      f (trainingSet p.1.1) p.1.2 * f (trainingSet p.1.1) p.2
      ∂(((Measure.pi fun _ : Fin m => D).prod D).prod D)) -
    2 * (∫ p : (Fin m → Z) × Z, f (trainingSet p.1) p.2 * f (removeAt p.1 i) (p.1 i)
      ∂((Measure.pi fun _ : Fin m => D).prod D)) +
    (∫ S, f (removeAt S i) (S i) * f (removeAt S j) (S j) ∂(Measure.pi fun _ : Fin m => D)) +
    M/(m:ℝ) * (∫ S, (∫ z, f (removeAt S i) z ∂D) ∂(Measure.pi fun _ : Fin m => D)) -
    1/(m:ℝ) * (∫ S, f (removeAt S i) (S i) * f (removeAt S j) (S j)
      ∂(Measure.pi fun _ : Fin m => D)) := by
  rw [deviation_expansion D f hf M hb hm, mixed_empirical D f hf M hb hm i,
    StabMoments.fresh_square D f (hf m) M hb, fresh_mixed D f hf M hb i]
  have h := empirical_second_moment_bound D f hf M hb hm i j hij
  rw [heldout_expectation D f hf M hb i] at h
  have hm' : (m:ℝ) ≠ 0 := by positivity
  have hcoef : ((m:ℝ)-1)/(m:ℝ) = 1 - 1/(m:ℝ) := by field_simp
  rw [hcoef] at h
  nlinarith
end LooMoments

open MeasureTheory
open StabGen.Hypothesis
open FoundationsML.Stability

theorem solution {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ) (M : ℝ)
    (hL : ∀ (y' : Y') (y : Y), 0 ≤ L y' y ∧ L y' y ≤ M)
    (A : LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable (fun p : (Fin n → X × Y) × (X × Y) =>
      Loss L (A (trainingSet p.1)) p.2))
    (m : ℕ) (hm : 2 ≤ m) (i j : Fin m) (hij : i ≠ j) :
    ∫ S : Fin m → X × Y,
        (GeneralizationError D L (A (trainingSet S)) - looError L A S) ^ 2
      ∂(Measure.pi fun _ : Fin m => D)
    ≤ ∫ p : ((Fin m → X × Y) × (X × Y)) × (X × Y),
          Loss L (A (trainingSet p.1.1)) p.1.2 * Loss L (A (trainingSet p.1.1)) p.2
        ∂(((Measure.pi fun _ : Fin m => D).prod D).prod D)
      - 2 * ∫ p : (Fin m → X × Y) × (X × Y),
          Loss L (A (trainingSet p.1)) p.2 * Loss L (A (removeAt p.1 i)) (p.1 i)
        ∂((Measure.pi fun _ : Fin m => D).prod D)
      + ∫ S : Fin m → X × Y,
          Loss L (A (removeAt S i)) (S i) * Loss L (A (removeAt S j)) (S j)
        ∂(Measure.pi fun _ : Fin m => D)
      + M / (m : ℝ) * ∫ S : Fin m → X × Y, GeneralizationError D L (A (removeAt S i))
        ∂(Measure.pi fun _ : Fin m => D)
      - 1 / (m : ℝ) * ∫ S : Fin m → X × Y,
          Loss L (A (removeAt S i)) (S i) * Loss L (A (removeAt S j)) (S j)
        ∂(Measure.pi fun _ : Fin m => D)  := by
  simpa only [GeneralizationError, looError, LooMoments.emp] using
    LooMoments.deviation_bound D (fun T z => Loss L (A T) z) hA M
      (fun T z => hL (A T z.1) z.2) (by omega) i j hij

#print axioms solution
