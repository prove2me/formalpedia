-- Prove2me | solution 1 for StabGen.Hypothesis.hypothesis_stability_generalization_bound
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-24T03:49:11.885925+00:00
-- url     : https://prove2.me/submissions/3d3cafc1-9da0-4478-82be-d647febe88e1

import Init
import Mathlib
import Definitions.Def_StabGen_Hypothesis_Setting
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_StabGen_Hypothesis_Stability

namespace EmpiricalPrior
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

set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace StabCross
variable {Z : Type*} [MeasurableSpace Z]
noncomputable def ell (F : Z → Z → Z → ℝ) (i j k : Fin 4) (S : Fin 4 → Z) : ℝ :=
  F (S i) (S j) (S k)
noncomputable def q (D : Measure Z) (F : Z → Z → Z → ℝ) (i j k a b c : Fin 4) : ℝ :=
  ∫ S, ell F i j k S * ell F a b c S ∂(Measure.pi fun _ : Fin 4 => D)
lemma q_perm (D : Measure Z) [IsProbabilityMeasure D] (F : Z → Z → Z → ℝ)
    (e : Equiv.Perm (Fin 4)) (i j k a b c : Fin 4) :
    q D F (e i) (e j) (e k) (e a) (e b) (e c) = q D F i j k a b c := by
  exact StabMoments.integral_permutation D e (fun S => ell F i j k S * ell F a b c S)
lemma q_swap_left (D : Measure Z) (F : Z → Z → Z → ℝ)
    (hs : ∀ a b z, F a b z = F b a z) (i j k a b c : Fin 4) :
    q D F i j k a b c = q D F j i k a b c := by
  unfold q
  apply integral_congr_ae
  filter_upwards [] with S
  change F (S i) (S j) (S k) * _ = F (S j) (S i) (S k) * _
  rw [hs (S i) (S j) (S k)]
lemma q_comm (D : Measure Z) (F : Z → Z → Z → ℝ) (i j k a b c : Fin 4) :
    q D F i j k a b c = q D F a b c i j k := by
  unfold q
  simp only [mul_comm]
noncomputable def d (D : Measure Z) (F : Z → Z → Z → ℝ) (i j k a b c : Fin 4) : ℝ :=
  ∫ S, |ell F i j k S - ell F a b c S| ∂(Measure.pi fun _ : Fin 4 => D)
lemma d_perm (D : Measure Z) [IsProbabilityMeasure D] (F : Z → Z → Z → ℝ)
    (e : Equiv.Perm (Fin 4)) (i j k a b c : Fin 4) :
    d D F (e i) (e j) (e k) (e a) (e b) (e c) = d D F i j k a b c := by
  exact StabMoments.integral_permutation D e (fun S => |ell F i j k S - ell F a b c S|)
lemma d_swap_left (D : Measure Z) (F : Z → Z → Z → ℝ)
    (hs : ∀ a b z, F a b z = F b a z) (i j k a b c : Fin 4) :
    d D F i j k a b c = d D F j i k a b c := by
  unfold d
  apply integral_congr_ae
  filter_upwards [] with S
  change |F (S i) (S j) (S k) - _| = |F (S j) (S i) (S k) - _|
  rw [hs (S i) (S j) (S k)]
lemma d_comm (D : Measure Z) (F : Z → Z → Z → ℝ) (i j k a b c : Fin 4) :
    d D F i j k a b c = d D F a b c i j k := by
  unfold d
  simp only [abs_sub_comm]
variable (D : Measure Z) [IsProbabilityMeasure D] (F : Z → Z → Z → ℝ)
    (hf : Measurable (fun p : Z × Z × Z => F p.1 p.2.1 p.2.2))
    (M : ℝ) (hb : ∀ a b z, 0 ≤ F a b z ∧ F a b z ≤ M)
include hf in
lemma ell_measurable (i j k : Fin 4) : Measurable (ell F i j k) := by
  change Measurable (fun S : Fin 4 → Z => F (S i) (S j) (S k))
  exact hf.comp (show Measurable (fun S : Fin 4 → Z => (S i,S j,S k)) from
    (measurable_pi_apply i).prodMk ((measurable_pi_apply j).prodMk (measurable_pi_apply k)))
include hb in
lemma ell_bound (i j k : Fin 4) (S : Fin 4 → Z) : |ell F i j k S| ≤ |M| := by
  rw [ell,abs_of_nonneg (hb _ _ _).1]
  exact (hb _ _ _).2.trans (le_abs_self M)
include hf hb in
lemma pair_integrable (i j k a b c : Fin 4) :
    Integrable (fun S => ell F i j k S * ell F a b c S) (Measure.pi fun _ : Fin 4 => D) :=
  StabMoments.bounded_product _ (ell_measurable F hf i j k) (ell_measurable F hf a b c) |M|
    (ell_bound F M hb i j k) (ell_bound F M hb a b c)
end StabCross

open MeasureTheory
namespace StabCross
variable {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (F : Z → Z → Z → ℝ) (hs : ∀ a b z, F a b z = F b a z)
include hs in
lemma q_012013 : q D F 0 1 2 0 1 3 = q D F 0 1 2 0 1 3 := by
  rfl
include hs in
lemma q_012201 : q D F 0 1 2 2 0 1 = q D F 0 1 2 0 2 1 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![0,1,2,3] : Fin 4 → Fin 4) (by decide)
  calc
    q D F 0 1 2 2 0 1 = q D F 0 1 2 2 0 1 := by
      simpa [e] using (q_perm D F e 0 1 2 2 0 1).symm
    _ = q D F 2 0 1 0 1 2 := q_comm D F 0 1 2 2 0 1
    _ = q D F 0 2 1 0 1 2 := q_swap_left D F hs 2 0 1 0 1 2
    _ = q D F 0 1 2 0 2 1 := q_comm D F 0 2 1 0 1 2
include hs in
lemma q_212013 : q D F 2 1 2 0 1 3 = q D F 0 1 0 1 2 3 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![2,1,0,3] : Fin 4 → Fin 4) (by decide)
  calc
    q D F 2 1 2 0 1 3 = q D F 0 1 0 2 1 3 := by
      simpa [e] using (q_perm D F e 2 1 2 0 1 3).symm
    _ = q D F 2 1 3 0 1 0 := q_comm D F 0 1 0 2 1 3
    _ = q D F 1 2 3 0 1 0 := q_swap_left D F hs 2 1 3 0 1 0
    _ = q D F 0 1 0 1 2 3 := q_comm D F 1 2 3 0 1 0
include hs in
lemma q_212201 : q D F 2 1 2 2 0 1 = q D F 0 1 0 0 2 1 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![2,1,0,3] : Fin 4 → Fin 4) (by decide)
  calc
    q D F 2 1 2 2 0 1 = q D F 0 1 0 0 2 1 := by
      simpa [e] using (q_perm D F e 2 1 2 2 0 1).symm
include hs in
lemma q_212123 : q D F 2 1 2 1 2 3 = q D F 0 1 0 0 1 2 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![3,1,0,2] : Fin 4 → Fin 4) (by decide)
  calc
    q D F 2 1 2 1 2 3 = q D F 0 1 0 1 0 2 := by
      simpa [e] using (q_perm D F e 2 1 2 1 2 3).symm
    _ = q D F 1 0 2 0 1 0 := q_comm D F 0 1 0 1 0 2
    _ = q D F 0 1 2 0 1 0 := q_swap_left D F hs 1 0 2 0 1 0
    _ = q D F 0 1 0 0 1 2 := q_comm D F 0 1 2 0 1 0
include hs in
lemma q_132013 : q D F 1 3 2 0 1 3 = q D F 0 1 2 0 2 3 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![1,0,3,2] : Fin 4 → Fin 4) (by decide)
  calc
    q D F 1 3 2 0 1 3 = q D F 0 2 3 1 0 2 := by
      simpa [e] using (q_perm D F e 1 3 2 0 1 3).symm
    _ = q D F 1 0 2 0 2 3 := q_comm D F 0 2 3 1 0 2
    _ = q D F 0 1 2 0 2 3 := q_swap_left D F hs 1 0 2 0 2 3
    _ = q D F 0 2 3 0 1 2 := q_comm D F 0 1 2 0 2 3
    _ = q D F 0 1 2 0 2 3 := q_comm D F 0 2 3 0 1 2
include hs in
lemma q_132123 : q D F 1 3 2 1 2 3 = q D F 0 1 2 0 2 1 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![3,0,1,2] : Fin 4 → Fin 4) (by decide)
  calc
    q D F 1 3 2 1 2 3 = q D F 0 2 1 0 1 2 := by
      simpa [e] using (q_perm D F e 1 3 2 1 2 3).symm
    _ = q D F 0 1 2 0 2 1 := q_comm D F 0 2 1 0 1 2
include hs in
lemma q_013132 : q D F 0 1 3 1 3 2 = q D F 0 1 2 0 2 3 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![1,0,3,2] : Fin 4 → Fin 4) (by decide)
  calc
    q D F 0 1 3 1 3 2 = q D F 1 0 2 0 2 3 := by
      simpa [e] using (q_perm D F e 0 1 3 1 3 2).symm
    _ = q D F 0 1 2 0 2 3 := q_swap_left D F hs 1 0 2 0 2 3
include hs in
lemma q_013131 : q D F 0 1 3 1 3 1 = q D F 0 1 0 0 2 1 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![2,0,3,1] : Fin 4 → Fin 4) (by decide)
  calc
    q D F 0 1 3 1 3 1 = q D F 2 0 1 0 1 0 := by
      simpa [e] using (q_perm D F e 0 1 3 1 3 1).symm
    _ = q D F 0 2 1 0 1 0 := q_swap_left D F hs 2 0 1 0 1 0
    _ = q D F 0 1 0 0 2 1 := q_comm D F 0 2 1 0 1 0
include hs in
lemma q_133132 : q D F 1 3 3 1 3 2 = q D F 0 1 0 0 1 2 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![3,1,2,0] : Fin 4 → Fin 4) (by decide)
  calc
    q D F 1 3 3 1 3 2 = q D F 1 0 0 1 0 2 := by
      simpa [e] using (q_perm D F e 1 3 3 1 3 2).symm
    _ = q D F 0 1 0 1 0 2 := q_swap_left D F hs 1 0 0 1 0 2
    _ = q D F 1 0 2 0 1 0 := q_comm D F 0 1 0 1 0 2
    _ = q D F 0 1 2 0 1 0 := q_swap_left D F hs 1 0 2 0 1 0
    _ = q D F 0 1 0 0 1 2 := q_comm D F 0 1 2 0 1 0
include hs in
lemma q_133131 : q D F 1 3 3 1 3 1 = q D F 0 1 0 0 1 1 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![2,0,3,1] : Fin 4 → Fin 4) (by decide)
  calc
    q D F 1 3 3 1 3 1 = q D F 0 1 1 0 1 0 := by
      simpa [e] using (q_perm D F e 1 3 3 1 3 1).symm
    _ = q D F 0 1 0 0 1 1 := q_comm D F 0 1 1 0 1 0
include hs in
lemma q_010011 : q D F 0 1 0 0 1 1 = q D F 0 1 0 0 1 1 := by
  rfl
include hs in
lemma q_012010 : q D F 0 1 2 0 1 0 = q D F 0 1 0 0 1 2 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![0,1,2,3] : Fin 4 → Fin 4) (by decide)
  calc
    q D F 0 1 2 0 1 0 = q D F 0 1 2 0 1 0 := by
      simpa [e] using (q_perm D F e 0 1 2 0 1 0).symm
    _ = q D F 0 1 0 0 1 2 := q_comm D F 0 1 2 0 1 0
include hs in
lemma d_012212 : d D F 0 1 2 2 1 2 = d D F 0 1 0 1 2 0 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![2,1,0,3] : Fin 4 → Fin 4) (by decide)
  calc
    d D F 0 1 2 2 1 2 = d D F 2 1 0 0 1 0 := by
      simpa [e] using (d_perm D F e 0 1 2 2 1 2).symm
    _ = d D F 1 2 0 0 1 0 := d_swap_left D F hs 2 1 0 0 1 0
    _ = d D F 0 1 0 1 2 0 := d_comm D F 1 2 0 0 1 0
include hs in
lemma d_212132 : d D F 2 1 2 1 3 2 = d D F 0 1 0 1 2 0 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![3,1,0,2] : Fin 4 → Fin 4) (by decide)
  calc
    d D F 2 1 2 1 3 2 = d D F 0 1 0 1 2 0 := by
      simpa [e] using (d_perm D F e 2 1 2 1 3 2).symm
include hs in
lemma d_013133 : d D F 0 1 3 1 3 3 = d D F 0 1 0 1 2 0 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![2,1,3,0] : Fin 4 → Fin 4) (by decide)
  calc
    d D F 0 1 3 1 3 3 = d D F 2 1 0 1 0 0 := by
      simpa [e] using (d_perm D F e 0 1 3 1 3 3).symm
    _ = d D F 1 2 0 1 0 0 := d_swap_left D F hs 2 1 0 1 0 0
    _ = d D F 1 0 0 1 2 0 := d_comm D F 1 2 0 1 0 0
    _ = d D F 0 1 0 1 2 0 := d_swap_left D F hs 1 0 0 1 2 0
    _ = d D F 1 2 0 0 1 0 := d_comm D F 0 1 0 1 2 0
    _ = d D F 0 1 0 1 2 0 := d_comm D F 1 2 0 0 1 0
include hs in
lemma d_010210 : d D F 0 1 0 2 1 0 = d D F 0 1 0 1 2 0 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![0,1,2,3] : Fin 4 → Fin 4) (by decide)
  calc
    d D F 0 1 0 2 1 0 = d D F 0 1 0 2 1 0 := by
      simpa [e] using (d_perm D F e 0 1 0 2 1 0).symm
    _ = d D F 2 1 0 0 1 0 := d_comm D F 0 1 0 2 1 0
    _ = d D F 1 2 0 0 1 0 := d_swap_left D F hs 2 1 0 0 1 0
    _ = d D F 0 1 0 1 2 0 := d_comm D F 1 2 0 0 1 0
include hs in
lemma cancellation :
    (q D F 0 1 2 0 1 3 - q D F 0 1 2 2 0 1 - q D F 2 1 2 0 1 3 + q D F 2 1 2 2 0 1) +
    (q D F 2 1 2 0 1 3 - q D F 2 1 2 1 2 3 - q D F 1 3 2 0 1 3 + q D F 1 3 2 1 2 3) +
    (q D F 0 1 3 1 3 2 - q D F 0 1 3 1 3 1 - q D F 1 3 3 1 3 2 + q D F 1 3 3 1 3 1) =
    q D F 0 1 2 0 1 3 + q D F 0 1 0 0 1 1 - 2 * q D F 0 1 2 0 1 0 := by
  rw [q_012201 D F hs, q_212013 D F hs, q_212201 D F hs, q_212123 D F hs, q_132013 D F hs, q_132123 D F hs, q_013132 D F hs, q_013131 D F hs, q_133132 D F hs, q_133131 D F hs, q_012010 D F hs]
  ring
end StabCross

set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace StabCross
variable {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (F : Z → Z → Z → ℝ)
    (hf : Measurable (fun p : Z × Z × Z => F p.1 p.2.1 p.2.2))
    (M : ℝ) (hb : ∀ a b z, 0 ≤ F a b z ∧ F a b z ≤ M)
noncomputable def dd (a b c d e f g h i j k l : Fin 4) : ℝ :=
  ∫ S, (ell F a b c S - ell F d e f S) * (ell F g h i S - ell F j k l S)
    ∂(Measure.pi fun _ : Fin 4 => D)
include hf hb in
lemma dd_expand (a b c d e f g h i j k l : Fin 4) :
    dd D F a b c d e f g h i j k l =
      q D F a b c g h i - q D F a b c j k l - q D F d e f g h i + q D F d e f j k l := by
  have h1 := pair_integrable D F hf M hb a b c g h i
  have h2 := pair_integrable D F hf M hb a b c j k l
  have h3 := pair_integrable D F hf M hb d e f g h i
  have h4 := pair_integrable D F hf M hb d e f j k l
  unfold dd
  simp_rw [sub_mul,mul_sub]
  have he := integral_sub (h1.sub h2) (h3.sub h4)
  dsimp only [Pi.sub_apply] at he
  rw [he,integral_sub h1 h2,integral_sub h3 h4]
  change q D F a b c g h i - q D F a b c j k l -
    (q D F d e f g h i - q D F d e f j k l) = _
  ring
include hb in
lemma ell_diff_bound (a b c d e f : Fin 4) (S : Fin 4 → Z) :
    |ell F a b c S - ell F d e f S| ≤ |M| := by
  have h1 := hb (S a) (S b) (S c)
  have h2 := hb (S d) (S e) (S f)
  apply le_trans (show |ell F a b c S - ell F d e f S| ≤ M from ?_) (le_abs_self M)
  apply abs_le.mpr
  dsimp [ell]
  constructor <;> linarith
include hf hb in
lemma dd_bound (a b c d e f g h i j k l : Fin 4) :
    dd D F a b c d e f g h i j k l ≤ M * StabCross.d D F a b c d e f := by
  have hp := StabMoments.bounded_product (Measure.pi fun _ : Fin 4 => D)
    ((ell_measurable F hf a b c).sub (ell_measurable F hf d e f))
    ((ell_measurable F hf g h i).sub (ell_measurable F hf j k l)) |M|
    (ell_diff_bound F M hb a b c d e f) (ell_diff_bound F M hb g h i j k l)
  have ha := StabMoments.bounded_integrable (Measure.pi fun _ : Fin 4 => D)
    ((ell_measurable F hf a b c).sub (ell_measurable F hf d e f)).abs |M|
    (fun S => by simpa only [abs_abs,Pi.sub_apply] using ell_diff_bound F M hb a b c d e f S)
  unfold dd StabCross.d
  rw [← integral_const_mul]
  apply integral_mono hp (ha.const_mul M)
  intro S
  have h1 := hb (S g) (S h) (S i)
  have h2 := hb (S j) (S k) (S l)
  have hh : |ell F g h i S - ell F j k l S| ≤ M := by
    apply abs_le.mpr
    dsimp [ell]
    constructor <;> linarith
  calc
    _ ≤ |(ell F a b c S - ell F d e f S) * (ell F g h i S - ell F j k l S)| := le_abs_self _
    _ = |ell F a b c S - ell F d e f S| * |ell F g h i S - ell F j k l S| := abs_mul _ _
    _ ≤ |ell F a b c S - ell F d e f S| * M := mul_le_mul_of_nonneg_left hh (abs_nonneg _)
    _ = _ := mul_comm _ _
include hf hb in
lemma cross_bound (hs : ∀ a b z, F a b z = F b a z) :
    q D F 0 1 2 0 1 3 + q D F 0 1 0 0 1 1 - 2 * q D F 0 1 2 0 1 0 ≤
      3 * M * d D F 0 1 0 2 1 0 := by
  have he : dd D F 0 1 2 2 1 2 0 1 3 2 0 1 +
      dd D F 2 1 2 1 3 2 0 1 3 1 2 3 + dd D F 0 1 3 1 3 3 1 3 2 1 3 1 =
      q D F 0 1 2 0 1 3 + q D F 0 1 0 0 1 1 - 2*q D F 0 1 2 0 1 0 := by
    rw [dd_expand D F hf M hb,dd_expand D F hf M hb,dd_expand D F hf M hb]
    exact cancellation D F hs
  have h1 := dd_bound D F hf M hb 0 1 2 2 1 2 0 1 3 2 0 1
  have h2 := dd_bound D F hf M hb 2 1 2 1 3 2 0 1 3 1 2 3
  have h3 := dd_bound D F hf M hb 0 1 3 1 3 3 1 3 2 1 3 1
  rw [d_012212 D F hs,← d_010210 D F hs] at h1
  rw [d_212132 D F hs,← d_010210 D F hs] at h2
  rw [d_013133 D F hs,← d_010210 D F hs] at h3
  linarith
#print axioms cross_bound
end StabCross

set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace StabCross
lemma training_cons {Z : Type*} {n : ℕ} (a : Z) (S : Fin n → Z) :
    StabGen.Hypothesis.trainingSet (Fin.cons a S) = a ::ₘ StabGen.Hypothesis.trainingSet S := by
  classical
  unfold StabGen.Hypothesis.trainingSet
  rw [Fin.univ_succ]
  simp [Finset.map_val,Multiset.map_map,Function.comp_def]
variable {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
lemma integral_cons {n : ℕ} (g : (Fin (n+1) → Z) → ℝ) (hg : Measurable g)
    (C : ℝ) (hb : ∀ S, |g S| ≤ C) :
    (∫ S, g S ∂(Measure.pi fun _ : Fin (n+1) => D)) =
      ∫ R, ∫ a, g (Fin.cons a R) ∂D ∂(Measure.pi fun _ : Fin n => D) := by
  have hm : Measurable (fun p : Z × (Fin n → Z) => Fin.cons (α := fun _ : Fin (n+1) => Z) p.1 p.2) := by
    apply measurable_pi_lambda
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using (measurable_fst : Measurable (fun p : Z × (Fin n → Z) => p.1))
    · simpa [Function.comp_def] using (measurable_pi_apply j).comp (measurable_snd : Measurable (fun p : Z × (Fin n → Z) => p.2))
  have hi := StabMoments.bounded_integrable (D.prod (Measure.pi fun _ : Fin n => D)) (hg.comp hm) C (fun p => hb _)
  have he := ((measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => D) 0).symm).integral_comp' g
  have hh : (∫ p : Z × (Fin n → Z),g (Fin.cons p.1 p.2) ∂(D.prod (Measure.pi fun _ => D))) =
      ∫ S,g S ∂(Measure.pi fun _ : Fin (n+1) => D) := by
    simpa [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Fin.insertNth_zero] using he
  rw [← hh]
  simpa only [Function.comp_apply] using integral_prod_symm _ hi
lemma integrate_first_measurable {n : ℕ} (g : (Fin (n+1) → Z) → ℝ) (hg : Measurable g) :
    Measurable (fun R : Fin n → Z => ∫ a, g (Fin.cons a R) ∂D) := by
  have hm : Measurable (fun p : (Fin n → Z) × Z => g (Fin.cons p.2 p.1)) := by
    apply hg.comp
    apply measurable_pi_lambda
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using (measurable_snd : Measurable (fun p : (Fin n → Z) × Z => p.2))
    · simpa [Function.comp_def] using (measurable_pi_apply j).comp (measurable_fst : Measurable (fun p : (Fin n → Z) × Z => p.1))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable
lemma integrate_first_bound {n : ℕ} (g : (Fin (n+1) → Z) → ℝ) (C : ℝ)
    (hb : ∀ S, |g S| ≤ C) (R : Fin n → Z) : |∫ a,g (Fin.cons a R) ∂D| ≤ C := by
  calc
    _ ≤ ∫ a, |g (Fin.cons a R)| ∂D := abs_integral_le_integral_abs
    _ ≤ ∫ _ : Z,C ∂D := integral_mono_of_nonneg (Filter.Eventually.of_forall fun a => abs_nonneg _)
      (integrable_const C) (Filter.Eventually.of_forall fun a => hb _)
    _ = C := by simp
lemma integral_four (g : (Fin 4 → Z) → ℝ) (hg : Measurable g) (C : ℝ) (hb : ∀ S, |g S| ≤ C) :
    (∫ S,g S ∂(Measure.pi fun _ : Fin 4 => D)) =
      ∫ d, ∫ c, ∫ b, ∫ a, g ![a,b,c,d] ∂D ∂D ∂D ∂D := by
  rw [integral_cons D g hg C hb]
  rw [integral_cons D _ (integrate_first_measurable D g hg) C (integrate_first_bound D g C hb)]
  rw [integral_cons D _ (integrate_first_measurable D _ (integrate_first_measurable D g hg)) C
    (integrate_first_bound D _ C (integrate_first_bound D g C hb))]
  rw [integral_cons D _ (integrate_first_measurable D _ (integrate_first_measurable D _ (integrate_first_measurable D g hg))) C
    (integrate_first_bound D _ C (integrate_first_bound D _ C (integrate_first_bound D g C hb)))]
  have he (S : Fin 0 → Z) (a b c d : Z) :
      Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d S))) = ![a,b,c,d] := by
    funext i
    fin_cases i <;> rfl
  simp_rw [he]
  simp
lemma integral_four_bacd (g : (Fin 4 → Z) → ℝ) (hg : Measurable g) (C : ℝ) (hb : ∀ S, |g S| ≤ C) :
    (∫ S,g S ∂(Measure.pi fun _ : Fin 4 => D)) =
      ∫ b, ∫ a, ∫ c, ∫ d, g ![a,b,c,d] ∂D ∂D ∂D ∂D := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![2,3,1,0] : Fin 4 → Fin 4) (by decide)
  rw [← StabMoments.integral_permutation D e g]
  have hm : Measurable (fun S : Fin 4 → Z => g (S ∘ e)) := hg.comp (by fun_prop)
  rw [integral_four D _ hm C (fun S => hb _)]
  have he (a b c d : Z) : ![a,b,c,d] ∘ e = ![c,d,b,a] := by
    funext i
    fin_cases i <;> rfl
  simp_rw [he]
end StabCross

set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace StabCross
variable {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (F : Z → Z → Z → ℝ)
    (hf : Measurable (fun p : Z × Z × Z => F p.1 p.2.1 p.2.2))
    (M : ℝ) (hb : ∀ a b z, 0 ≤ F a b z ∧ F a b z ≤ M)
include hf hb in
lemma q_iterated (a b c d e f : Fin 4) : q D F a b c d e f =
    ∫ y, ∫ x, ∫ z, ∫ w,
      ell F a b c ![x,y,z,w] * ell F d e f ![x,y,z,w] ∂D ∂D ∂D ∂D := by
  apply integral_four_bacd D _ ((ell_measurable F hf a b c).mul (ell_measurable F hf d e f)) (|M| * |M|)
  intro S
  rw [Pi.mul_apply,abs_mul]
  exact mul_le_mul (ell_bound F M hb a b c S) (ell_bound F M hb d e f S) (abs_nonneg _) (abs_nonneg _)
include hf hb in
lemma q_fresh : q D F 0 1 2 0 1 3 =
    ∫ b, ∫ a, (∫ z, F a b z ∂D)^2 ∂D ∂D := by
  rw [q_iterated D F hf M hb]
  simp [ell,integral_const_mul,integral_mul_const,pow_two]
include hf hb in
lemma q_training : q D F 0 1 0 0 1 1 =
    ∫ b, ∫ a, F a b a * F a b b ∂D ∂D := by
  rw [q_iterated D F hf M hb]
  simp [ell]
include hf hb in
lemma q_mixed : q D F 0 1 2 0 1 0 =
    ∫ b, ∫ a, (∫ z, F a b z ∂D) * F a b a ∂D ∂D := by
  rw [q_iterated D F hf M hb]
  simp [ell,integral_mul_const]
include hf hb in
lemma d_replacement : d D F 0 1 0 2 1 0 =
    ∫ b, ∫ a, ∫ z, |F a b a - F z b a| ∂D ∂D ∂D := by
  unfold d
  have hm : Measurable (fun S => |ell F 0 1 0 S - ell F 2 1 0 S|) := by
    simpa only [Pi.sub_apply] using ((ell_measurable F hf 0 1 0).sub (ell_measurable F hf 2 1 0)).abs
  rw [integral_four_bacd D _ hm |M|]
  · simp [ell]
  · intro S
    simpa only [abs_abs] using ell_diff_bound F M hb 0 1 0 2 1 0 S
include hf hb in
lemma nested_cross_bound (hs : ∀ a b z, F a b z = F b a z) :
    (∫ b, ∫ a, (∫ z, F a b z ∂D)^2 ∂D ∂D) +
    (∫ b, ∫ a, F a b a * F a b b ∂D ∂D) -
    2*(∫ b, ∫ a, (∫ z,F a b z ∂D)*F a b a ∂D ∂D) ≤
      3*M*(∫ b, ∫ a, ∫ z, |F a b a - F z b a| ∂D ∂D ∂D) := by
  rw [← q_fresh D F hf M hb,← q_training D F hf M hb,← q_mixed D F hf M hb,← d_replacement D F hf M hb]
  exact cross_bound D F hf M hb hs
#print axioms nested_cross_bound
end StabCross

set_option backward.isDefEq.respectTransparency false
open MeasureTheory StabGen.Hypothesis
namespace StabCross
variable {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
lemma integral_cons_two {n : ℕ} (g : (Fin (n+2) → Z) → ℝ) (hg : Measurable g)
    (C : ℝ) (hb : ∀ S, |g S| ≤ C) :
    (∫ S, g S ∂(Measure.pi fun _ : Fin (n+2) => D)) =
      ∫ R, ∫ b, ∫ a, g (Fin.cons a (Fin.cons b R)) ∂D ∂D ∂(Measure.pi fun _ : Fin n => D) := by
  rw [integral_cons D g hg C hb]
  rw [integral_cons D _ (integrate_first_measurable D g hg) C (integrate_first_bound D g C hb)]
variable (f : Multiset Z → Z → ℝ)
    (hf : ∀ n, Measurable (fun p : (Fin n → Z) × Z => f (trainingSet p.1) p.2))
    (M : ℝ) (hb : ∀ T z, 0 ≤ f T z ∧ f T z ≤ M)
include hf in
lemma two_point_measurable {n : ℕ} (R : Fin n → Z) :
    Measurable (fun p : Z × Z × Z => f (p.1 ::ₘ p.2.1 ::ₘ trainingSet R) p.2.2) := by
  have hm : Measurable (fun p : Z × Z × Z =>
      ((Fin.cons p.1 (Fin.cons p.2.1 R) : Fin (n+2) → Z),p.2.2)) := by
    apply Measurable.prodMk _ (by fun_prop)
    apply measurable_pi_lambda
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using (measurable_fst : Measurable (fun p : Z × Z × Z => p.1))
    · refine Fin.cases ?_ (fun k => ?_) j
      · simpa [Function.comp_def] using (measurable_fst.comp measurable_snd : Measurable (fun p : Z × Z × Z => p.2.1))
      · simp
  simpa only [Function.comp_def,training_cons] using (hf (n+2)).comp hm
include hf hb in
lemma conditioned_training_cross {n : ℕ} (R : Fin n → Z) :
    (∫ b, ∫ a, (∫ z, f (a ::ₘ b ::ₘ trainingSet R) z ∂D)^2 ∂D ∂D) +
    (∫ b, ∫ a, f (a ::ₘ b ::ₘ trainingSet R) a * f (a ::ₘ b ::ₘ trainingSet R) b ∂D ∂D) -
    2*(∫ b, ∫ a, (∫ z,f (a ::ₘ b ::ₘ trainingSet R) z ∂D)*f (a ::ₘ b ::ₘ trainingSet R) a ∂D ∂D) ≤
      3*M*(∫ b, ∫ a, ∫ z, |f (a ::ₘ b ::ₘ trainingSet R) a - f (z ::ₘ b ::ₘ trainingSet R) a| ∂D ∂D ∂D) := by
  apply nested_cross_bound D (fun a b z => f (a ::ₘ b ::ₘ trainingSet R) z)
    (two_point_measurable f hf R) M (fun a b z => hb _ _)
  intro a b z
  rw [Multiset.cons_swap]
#print axioms conditioned_training_cross
end StabCross

set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace StabCross
variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : Measure Z) [IsProbabilityMeasure D]
    (F : Ω → Z → Z → Z → ℝ)
    (hf : Measurable (fun p : Ω × (Z × Z × Z) => F p.1 p.2.1 p.2.2.1 p.2.2.2))
    (M : ℝ) (hb : ∀ r a b z, 0 ≤ F r a b z ∧ F r a b z ≤ M)
include hf in
lemma context_ell_measurable (a b c : Fin 4) :
    Measurable (fun p : Ω × (Fin 4 → Z) => ell (F p.1) a b c p.2) := by
  change Measurable (fun p : Ω × (Fin 4 → Z) => F p.1 (p.2 a) (p.2 b) (p.2 c))
  exact hf.comp (show Measurable (fun p : Ω × (Fin 4 → Z) => (p.1,(p.2 a,p.2 b,p.2 c))) from
    measurable_fst.prodMk (((measurable_pi_apply a).comp measurable_snd).prodMk
      (((measurable_pi_apply b).comp measurable_snd).prodMk ((measurable_pi_apply c).comp measurable_snd))))
include hf in
lemma context_q_measurable (a b c d e f : Fin 4) :
    Measurable (fun r => q D (F r) a b c d e f) := by
  exact ((context_ell_measurable F hf a b c).mul (context_ell_measurable F hf d e f)).stronglyMeasurable.integral_prod_right'.measurable
include hf in
lemma context_d_measurable (a b c d e f : Fin 4) :
    Measurable (fun r => StabCross.d D (F r) a b c d e f) := by
  exact ((context_ell_measurable F hf a b c).sub (context_ell_measurable F hf d e f)).abs.stronglyMeasurable.integral_prod_right'.measurable
include hb in
lemma context_q_bound (a b c d e f : Fin 4) (r : Ω) :
    |q D (F r) a b c d e f| ≤ |M| * |M| := by
  unfold q
  calc
    _ ≤ ∫ S, |ell (F r) a b c S * ell (F r) d e f S| ∂(Measure.pi fun _ : Fin 4 => D) := abs_integral_le_integral_abs
    _ ≤ ∫ _S : Fin 4 → Z, |M| * |M| ∂(Measure.pi fun _ : Fin 4 => D) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun S => abs_nonneg _) (integrable_const _)
      filter_upwards [] with S
      rw [abs_mul]
      exact mul_le_mul (ell_bound (F r) M (hb r) a b c S) (ell_bound (F r) M (hb r) d e f S) (abs_nonneg _) (abs_nonneg _)
    _ = _ := by simp
include hb in
lemma context_d_bound (a b c d e f : Fin 4) (r : Ω) :
    |StabCross.d D (F r) a b c d e f| ≤ |M| := by
  unfold StabCross.d
  calc
    _ ≤ ∫ S, |ell (F r) a b c S - ell (F r) d e f S| ∂(Measure.pi fun _ : Fin 4 => D) := by
      simpa only [abs_abs] using (abs_integral_le_integral_abs (f := fun S => |ell (F r) a b c S - ell (F r) d e f S|) (μ := Measure.pi fun _ : Fin 4 => D))
    _ ≤ ∫ _S : Fin 4 → Z, |M| ∂(Measure.pi fun _ : Fin 4 => D) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun S => abs_nonneg _) (integrable_const _)
      exact Filter.Eventually.of_forall (ell_diff_bound (F r) M (hb r) a b c d e f)
    _ = _ := by simp
include hf hb in
lemma random_context_cross (hs : ∀ r a b z, F r a b z = F r b a z) :
    (∫ r, q D (F r) 0 1 2 0 1 3 ∂μ) + (∫ r, q D (F r) 0 1 0 0 1 1 ∂μ) -
    2*(∫ r,q D (F r) 0 1 2 0 1 0 ∂μ) ≤ 3*M*(∫ r,StabCross.d D (F r) 0 1 0 2 1 0 ∂μ) := by
  have hi (a b c d e f : Fin 4) := StabMoments.bounded_integrable μ
    (context_q_measurable D F hf a b c d e f) (|M| * |M|) (context_q_bound D F M hb a b c d e f)
  have hd := StabMoments.bounded_integrable μ (context_d_measurable D F hf 0 1 0 2 1 0) |M|
    (context_d_bound D F M hb 0 1 0 2 1 0)
  have hleft := integral_sub ((hi 0 1 2 0 1 3).add (hi 0 1 0 0 1 1)) ((hi 0 1 2 0 1 0).const_mul 2)
  dsimp only [Pi.add_apply] at hleft
  rw [integral_add (hi 0 1 2 0 1 3) (hi 0 1 0 0 1 1),integral_const_mul] at hleft
  rw [← hleft,← integral_const_mul]
  apply integral_mono (((hi 0 1 2 0 1 3).add (hi 0 1 0 0 1 1)).sub ((hi 0 1 2 0 1 0).const_mul 2)) (hd.const_mul (3*M))
  intro r
  have hr : Measurable (fun p : Z × Z × Z => F r p.1 p.2.1 p.2.2) :=
    hf.comp (measurable_const.prodMk measurable_id)
  exact cross_bound D (F r) hr M (hb r) (hs r)
#print axioms random_context_cross
end StabCross

set_option backward.isDefEq.respectTransparency false
open MeasureTheory StabGen.Hypothesis
namespace StabCross
variable {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (f : Multiset Z → Z → ℝ)
    (hf : ∀ n, Measurable (fun p : (Fin n → Z) × Z => f (trainingSet p.1) p.2))
    (M : ℝ) (hb : ∀ T z, 0 ≤ f T z ∧ f T z ≤ M)
include hf in
lemma training_context_measurable (n : ℕ) :
    Measurable (fun p : (Fin n → Z) × (Z × Z × Z) =>
      f (p.2.1 ::ₘ p.2.2.1 ::ₘ trainingSet p.1) p.2.2.2) := by
  have hm : Measurable (fun p : (Fin n → Z) × (Z × Z × Z) =>
      ((Fin.cons p.2.1 (Fin.cons p.2.2.1 p.1) : Fin (n+2) → Z),p.2.2.2)) := by
    apply Measurable.prodMk _ (by fun_prop)
    apply measurable_pi_lambda
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [Function.comp_def] using (measurable_fst.comp measurable_snd :
        Measurable (fun p : (Fin n → Z) × (Z × Z × Z) => p.2.1))
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp only [Fin.cons_succ,Fin.cons_zero]
        fun_prop
      · simp only [Fin.cons_succ]
        fun_prop
  simpa only [Function.comp_def,training_cons] using (hf (n+2)).comp hm
include hf hb in
lemma random_training_cross (n : ℕ) :
    (∫ R, q D (fun a b z => f (a ::ₘ b ::ₘ trainingSet R) z) 0 1 2 0 1 3
      ∂(Measure.pi fun _ : Fin n => D)) +
    (∫ R, q D (fun a b z => f (a ::ₘ b ::ₘ trainingSet R) z) 0 1 0 0 1 1
      ∂(Measure.pi fun _ : Fin n => D)) -
    2*(∫ R,q D (fun a b z => f (a ::ₘ b ::ₘ trainingSet R) z) 0 1 2 0 1 0
      ∂(Measure.pi fun _ : Fin n => D)) ≤
    3*M*(∫ R,d D (fun a b z => f (a ::ₘ b ::ₘ trainingSet R) z) 0 1 0 2 1 0
      ∂(Measure.pi fun _ : Fin n => D)) := by
  apply random_context_cross (Measure.pi fun _ : Fin n => D) D
    (fun R a b z => f (a ::ₘ b ::ₘ trainingSet R) z)
    (training_context_measurable f hf n) M (fun R a b z => hb _ _)
  intro R a b z
  rw [Multiset.cons_swap]
#print axioms random_training_cross
end StabCross

open MeasureTheory
open scoped BigOperators
namespace StabMoments
open StabGen.Hypothesis
noncomputable def emp {Z : Type*} {m : ℕ} (f : Multiset Z → Z → ℝ) (S : Fin m → Z) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, f (trainingSet S) (S i)

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
    (hf : Measurable (fun p : (Fin m → Z) × Z => f (trainingSet p.1) p.2))
    (M : ℝ) (hb : ∀ T z, 0 ≤ f T z ∧ f T z ≤ M)
include hf hb

lemma empirical_second_moment (hm : 0 < m) (i j : Fin m) (hij : i ≠ j) :
    (∫ S, (emp f S)^2 ∂(Measure.pi fun _ : Fin m => D)) =
      (1 / (m : ℝ)) * (∫ S, (f (trainingSet S) (S i))^2 ∂(Measure.pi fun _ : Fin m => D)) +
      (((m : ℝ)-1) / (m : ℝ)) *
        (∫ S, f (trainingSet S) (S i) * f (trainingSet S) (S j)
          ∂(Measure.pi fun _ : Fin m => D)) := by
  let μ := Measure.pi (fun _ : Fin m => D)
  let a := ∫ S, (f (trainingSet S) (S i))^2 ∂μ
  let b := ∫ S, f (trainingSet S) (S i) * f (trainingSet S) (S j) ∂μ
  have hpair (k l : Fin m) :
      (∫ S, f (trainingSet S) (S k) * f (trainingSet S) (S l) ∂μ) =
      if k = l then a else b := by
    by_cases h : k = l
    · subst l
      simpa [a, μ, pow_two] using diagonal_invariant D f k i (fun x => x*x)
    · simpa only [if_neg h, b] using pair_invariant D f k l i j h hij
  have hpoint (S : Fin m → Z) : (emp f S)^2 =
      (1 / (m : ℝ))^2 * ∑ k, ∑ l, f (trainingSet S) (S k) * f (trainingSet S) (S l) := by
    unfold emp
    rw [mul_pow, pow_two (∑ k, f (trainingSet S) (S k)), Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  have hmi : (m : ℝ) ≠ 0 := by positivity
  calc
    _ = (1 / (m : ℝ))^2 * ∫ S, ∑ k, ∑ l,
        f (trainingSet S) (S k) * f (trainingSet S) (S l) ∂μ := by
      simp_rw [hpoint]
      exact integral_const_mul _ _
    _ = (1 / (m : ℝ))^2 * ∑ k, ∑ l,
        ∫ S, f (trainingSet S) (S k) * f (trainingSet S) (S l) ∂μ := by
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
      M / (m : ℝ) * (∫ S, f (trainingSet S) (S i) ∂(Measure.pi fun _ : Fin m => D)) +
      (((m : ℝ)-1) / (m : ℝ)) *
        (∫ S, f (trainingSet S) (S i) * f (trainingSet S) (S j)
          ∂(Measure.pi fun _ : Fin m => D)) := by
  rw [empirical_second_moment D f hf M hb hm i j hij]
  have h : (∫ S, (f (trainingSet S) (S i))^2 ∂(Measure.pi fun _ : Fin m => D)) ≤
      M * ∫ S, f (trainingSet S) (S i) ∂(Measure.pi fun _ : Fin m => D) := by
    rw [← integral_const_mul]
    apply integral_mono
    · simpa only [pow_two] using loss_product_integrable D f hf M hb i i
    · exact (loss_integrable D f hf M hb i).const_mul M
    · intro S
      have h := hb (trainingSet S) (S i)
      nlinarith [mul_nonneg h.1 (sub_nonneg.mpr h.2)]
  have := mul_le_mul_of_nonneg_left h (show 0 ≤ 1/(m:ℝ) by positivity)
  apply add_le_add _ le_rfl
  convert this using 1 <;> ring

lemma mixed_empirical (hm : 0 < m) (i : Fin m) :
    (∫ S, (∫ z, f (trainingSet S) z ∂D) * emp f S ∂(Measure.pi fun _ : Fin m => D)) =
    ∫ S, (∫ z, f (trainingSet S) z ∂D) * f (trainingSet S) (S i)
      ∂(Measure.pi fun _ : Fin m => D) := by
  have hpoint (S : Fin m → Z) :
      (∫ z, f (trainingSet S) z ∂D) * emp f S =
      (1/(m:ℝ)) * ∑ k, (∫ z, f (trainingSet S) z ∂D) * f (trainingSet S) (S k) := by
    simp only [emp, ← Finset.mul_sum]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul, integral_finsetSum _ (fun k _ => mixed_integrable D f hf M hb k)]
  have heq (k : Fin m) := mixed_invariant D f (fun T => ∫ z, f T z ∂D) k i
  simp_rw [heq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hm' : (m:ℝ) ≠ 0 := by positivity
  field_simp
end StabMoments

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

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
namespace StabMoments
open StabGen.Hypothesis
variable {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    {m : ℕ} (f : Multiset Z → Z → ℝ)
    (hf : Measurable (fun p : (Fin m → Z) × Z => f (trainingSet p.1) p.2))
    (M : ℝ) (hb : ∀ T z, 0 ≤ f T z ∧ f T z ≤ M)
include hf hb

lemma emp_measurable : Measurable (fun S : Fin m → Z => emp f S) := by
  unfold emp
  exact measurable_const.mul (Finset.measurable_sum _ (fun i _ => loss_measurable f hf i))

lemma emp_bound (hm : 0 < m) (S : Fin m → Z) : |emp f S| ≤ |M| := by
  have hs : |∑ i, f (trainingSet S) (S i)| ≤ (m : ℝ)*|M| := by
    calc
      _ ≤ ∑ i, |f (trainingSet S) (S i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin m, |M| := Finset.sum_le_sum (fun i _ => loss_bound f M hb S i)
      _ = _ := by simp
  have hm' : (m:ℝ) ≠ 0 := by positivity
  calc
    _ = (1/(m:ℝ))*|∑ i, f (trainingSet S) (S i)| := by
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
    simpa only [pow_two] using bounded_product μ (risk_measurable D f hf)
      (risk_measurable D f hf) |M| (risk_bound D f hf M hb) (risk_bound D f hf M hb)
  have he : Integrable (fun S : Fin m → Z => (emp f S)^2) μ := by
    simpa only [pow_two] using bounded_product μ (emp_measurable f hf M hb)
      (emp_measurable f hf M hb) |M| (emp_bound f hf M hb hm) (emp_bound f hf M hb hm)
  have hx : Integrable (fun S : Fin m → Z => (∫ z, f (trainingSet S) z ∂D) * emp f S) μ :=
    bounded_product μ (risk_measurable D f hf) (emp_measurable f hf M hb) |M|
      (risk_bound D f hf M hb) (emp_bound f hf M hb hm)
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
    2 * (∫ p : (Fin m → Z) × Z, f (trainingSet p.1) p.2 * f (trainingSet p.1) (p.1 i)
      ∂((Measure.pi fun _ : Fin m => D).prod D)) +
    (∫ S, f (trainingSet S) (S i) * f (trainingSet S) (S j) ∂(Measure.pi fun _ : Fin m => D)) +
    M/(m:ℝ) * (∫ S, f (trainingSet S) (S i) ∂(Measure.pi fun _ : Fin m => D)) -
    1/(m:ℝ) * (∫ S, f (trainingSet S) (S i) * f (trainingSet S) (S j)
      ∂(Measure.pi fun _ : Fin m => D)) := by
  rw [deviation_expansion D f hf M hb hm, mixed_empirical D f hf M hb hm i,
    fresh_square D f hf M hb, fresh_mixed D f hf M hb i]
  have h := empirical_second_moment_bound D f hf M hb hm i j hij
  have hm' : (m:ℝ) ≠ 0 := by positivity
  have hcoef : ((m:ℝ)-1)/(m:ℝ) = 1 - 1/(m:ℝ) := by field_simp
  rw [hcoef] at h
  nlinarith
end StabMoments

open MeasureTheory
namespace StabDiagonal
lemma pair_gap (a b M : ℝ) (ha : 0 ≤ a ∧ a ≤ M) (hb : 0 ≤ b ∧ b ≤ M) :
    a * (M-b) ≤ M^2/2 + (M/2)*(a-b) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2),mul_nonneg ha.1 hb.1]
lemma equal_mean_pair {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (a b : Ω → ℝ) (ha : Measurable a) (hb : Measurable b) (M : ℝ)
    (ba : ∀ x, 0 ≤ a x ∧ a x ≤ M) (bb : ∀ x, 0 ≤ b x ∧ b x ≤ M)
    (he : (∫ x, a x ∂μ) = ∫ x, b x ∂μ) :
    (∫ x, a x * (M-b x) ∂μ) ≤ M^2/2 := by
  have ba' (x : Ω) : |a x| ≤ |M| := by rw [abs_of_nonneg (ba x).1]; exact (ba x).2.trans (le_abs_self M)
  have bb' (x : Ω) : |b x| ≤ |M| := by rw [abs_of_nonneg (bb x).1]; exact (bb x).2.trans (le_abs_self M)
  have bc' (x : Ω) : |M-b x| ≤ |M| := by
    rw [abs_of_nonneg (sub_nonneg.mpr (bb x).2)]
    exact (sub_le_self M (bb x).1).trans (le_abs_self M)
  have ia := StabMoments.bounded_integrable μ ha |M| ba'
  have ib := StabMoments.bounded_integrable μ hb |M| bb'
  have iac := StabMoments.bounded_product μ ha (measurable_const.sub hb) |M| ba' bc'
  calc
    _ ≤ ∫ x, (M^2/2 + (M/2)*(a x-b x)) ∂μ :=
      integral_mono iac ((integrable_const _).add ((ia.sub ib).const_mul (M/2)))
        (fun x => pair_gap _ _ _ (ba x) (bb x))
    _ = M^2/2 := by
      change (∫ x, (M^2/2 + (M/2)*((a-b) x)) ∂μ) = _
      rw [integral_add (integrable_const _) ((ia.sub ib).const_mul (M/2)),
        integral_const_mul]
      simp only [Pi.sub_apply]
      rw [integral_sub ia ib,he]
      simp
lemma training_pair {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    {m : ℕ} (f : Multiset Z → Z → ℝ)
    (hf : Measurable (fun p : (Fin m → Z) × Z => f (StabGen.Hypothesis.trainingSet p.1) p.2))
    (M : ℝ) (hb : ∀ T z, 0 ≤ f T z ∧ f T z ≤ M) (i j : Fin m) :
    (∫ S, f (StabGen.Hypothesis.trainingSet S) (S i) *
      (M-f (StabGen.Hypothesis.trainingSet S) (S j)) ∂(Measure.pi fun _ : Fin m => D)) ≤ M^2/2 := by
  apply equal_mean_pair _ _ _ (StabMoments.loss_measurable f hf i)
    (StabMoments.loss_measurable f hf j) M (fun S => hb _ _) (fun S => hb _ _)
  exact StabMoments.diagonal_invariant D f i j id
#print axioms training_pair
end StabDiagonal

set_option backward.isDefEq.respectTransparency false
open MeasureTheory StabGen.Hypothesis
namespace StabFull
variable {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (f : Multiset Z → Z → ℝ)
    (hf : ∀ n, Measurable (fun p : (Fin n → Z) × Z => f (trainingSet p.1) p.2))
    (M : ℝ) (hb : ∀ T z, 0 ≤ f T z ∧ f T z ≤ M)
include hf hb in
lemma fresh_identification (n : ℕ) :
    (∫ S, (∫ z, f (trainingSet S) z ∂D)^2 ∂(Measure.pi fun _ : Fin (n+2) => D)) =
    ∫ R, StabCross.q D (fun a b z => f (a ::ₘ b ::ₘ trainingSet R) z) 0 1 2 0 1 3
      ∂(Measure.pi fun _ : Fin n => D) := by
  have hB (S : Fin (n+2) → Z) : |(∫ z, f (trainingSet S) z ∂D)^2| ≤ |M|^2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (StabMoments.risk_bound D f (hf _) M hb S) _
  rw [StabCross.integral_cons_two D _ ((StabMoments.risk_measurable D f (hf _)).pow_const 2) (|M|^2) hB]
  apply integral_congr_ae
  filter_upwards [] with R
  rw [StabCross.q_fresh D _ (StabCross.two_point_measurable f hf R) M (fun a b z => hb _ _)]
  simp only [StabCross.training_cons]
include hf hb in
lemma training_identification (n : ℕ) :
    (∫ S, f (trainingSet S) (S 0) * f (trainingSet S) (S 1)
      ∂(Measure.pi fun _ : Fin (n+2) => D)) =
    ∫ R, StabCross.q D (fun a b z => f (a ::ₘ b ::ₘ trainingSet R) z) 0 1 0 0 1 1
      ∂(Measure.pi fun _ : Fin n => D) := by
  have hB (S : Fin (n+2) → Z) : |f (trainingSet S) (S 0) * f (trainingSet S) (S 1)| ≤ |M| * |M| := by
    rw [abs_mul]
    exact mul_le_mul (StabMoments.loss_bound f M hb S 0) (StabMoments.loss_bound f M hb S 1)
      (abs_nonneg _) (abs_nonneg _)
  rw [StabCross.integral_cons_two D (fun S : Fin (n+2) → Z => f (trainingSet S) (S 0) * f (trainingSet S) (S 1))
    ((StabMoments.loss_measurable f (hf _) 0).mul (StabMoments.loss_measurable f (hf _) 1)) (|M| * |M|) hB]
  apply integral_congr_ae
  filter_upwards [] with R
  rw [StabCross.q_training D _ (StabCross.two_point_measurable f hf R) M (fun a b z => hb _ _)]
  simp only [StabCross.training_cons,Fin.cons_zero,Fin.cons_one]
include hf hb in
lemma mixed_identification (n : ℕ) :
    (∫ S, (∫ z, f (trainingSet S) z ∂D) * f (trainingSet S) (S 0)
      ∂(Measure.pi fun _ : Fin (n+2) => D)) =
    ∫ R, StabCross.q D (fun a b z => f (a ::ₘ b ::ₘ trainingSet R) z) 0 1 2 0 1 0
      ∂(Measure.pi fun _ : Fin n => D) := by
  have hB (S : Fin (n+2) → Z) : |(∫ z, f (trainingSet S) z ∂D) * f (trainingSet S) (S 0)| ≤ |M| * |M| := by
    rw [abs_mul]
    exact mul_le_mul (StabMoments.risk_bound D f (hf _) M hb S) (StabMoments.loss_bound f M hb S 0)
      (abs_nonneg _) (abs_nonneg _)
  rw [StabCross.integral_cons_two D (fun S : Fin (n+2) → Z => (∫ z, f (trainingSet S) z ∂D) * f (trainingSet S) (S 0))
    ((StabMoments.risk_measurable D f (hf _)).mul (StabMoments.loss_measurable f (hf _) 0)) (|M| * |M|) hB]
  apply integral_congr_ae
  filter_upwards [] with R
  rw [StabCross.q_mixed D _ (StabCross.two_point_measurable f hf R) M (fun a b z => hb _ _)]
  simp only [StabCross.training_cons,Fin.cons_zero]
end StabFull

set_option backward.isDefEq.respectTransparency false
open MeasureTheory StabGen.Hypothesis
namespace StabFull
variable {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (f : Multiset Z → Z → ℝ)
    (hf : ∀ n, Measurable (fun p : (Fin n → Z) × Z => f (trainingSet p.1) p.2))
    (M : ℝ) (hb : ∀ T z, 0 ≤ f T z ∧ f T z ≤ M)
lemma replace_measurable {m : ℕ} (i : Fin m) :
    Measurable (fun p : (Fin m → Z) × Z => replaceAt p.1 i p.2) := by
  classical
  apply measurable_pi_lambda
  intro k
  by_cases h : k = i
  · subst k; simpa [replaceAt] using (measurable_snd : Measurable (fun p : (Fin m → Z) × Z => p.2))
  · simpa [replaceAt,h,Function.comp_def] using ((measurable_pi_apply k).comp (measurable_fst : Measurable (fun p : (Fin m → Z) × Z => p.1)))
include hf in
lemma replacement_measurable {m : ℕ} (i : Fin m) : Measurable (fun p : (Fin m → Z) × Z =>
    |f (trainingSet p.1) (p.1 i) - f (trainingSet (replaceAt p.1 i p.2)) (p.1 i)|) := by
  exact (((StabMoments.loss_measurable f (hf m) i).comp measurable_fst).sub
    ((hf m).comp ((replace_measurable i).prodMk ((measurable_pi_apply i).comp measurable_fst)))).abs
include hb in
lemma replacement_bound {m : ℕ} (i : Fin m) (p : (Fin m → Z) × Z) :
    |f (trainingSet p.1) (p.1 i) - f (trainingSet (replaceAt p.1 i p.2)) (p.1 i)| ≤ |M| := by
  apply le_trans _ (le_abs_self M)
  apply abs_le.mpr
  constructor <;> linarith [(hb (trainingSet p.1) (p.1 i)).1,
    (hb (trainingSet p.1) (p.1 i)).2,(hb (trainingSet (replaceAt p.1 i p.2)) (p.1 i)).1,
    (hb (trainingSet (replaceAt p.1 i p.2)) (p.1 i)).2]
include hf hb in
lemma replacement_prod {m : ℕ} (i : Fin m) :
    (∫ p : (Fin m → Z) × Z,
      |f (trainingSet p.1) (p.1 i) - f (trainingSet (replaceAt p.1 i p.2)) (p.1 i)|
      ∂((Measure.pi fun _ : Fin m => D).prod D)) =
    ∫ S, ∫ z, |f (trainingSet S) (S i) - f (trainingSet (replaceAt S i z)) (S i)| ∂D
      ∂(Measure.pi fun _ : Fin m => D) := by
  apply integral_prod
  apply StabMoments.bounded_integrable _ (replacement_measurable f hf i) |M|
  intro p
  simpa only [abs_abs] using replacement_bound f M hb i p
include hf in
lemma replacement_average_measurable {m : ℕ} (i : Fin m) :
    Measurable (fun S => ∫ z, |f (trainingSet S) (S i) - f (trainingSet (replaceAt S i z)) (S i)| ∂D) :=
  (replacement_measurable f hf i).stronglyMeasurable.integral_prod_right'.measurable
include hb in
lemma replacement_average_bound {m : ℕ} (i : Fin m) (S : Fin m → Z) :
    |∫ z, |f (trainingSet S) (S i) - f (trainingSet (replaceAt S i z)) (S i)| ∂D| ≤ |M| := by
  calc
    _ ≤ ∫ z, abs (|f (trainingSet S) (S i) - f (trainingSet (replaceAt S i z)) (S i)|) ∂D :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _ : Z, |M| ∂D := integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
      (integrable_const _) (Filter.Eventually.of_forall fun z => by simpa only [abs_abs] using replacement_bound f M hb i (S,z))
    _ = _ := by simp
lemma replace_permutation {m : ℕ} (S : Fin m → Z) (i : Fin m) (z : Z) (e : Equiv.Perm (Fin m)) :
    replaceAt (S ∘ e) i z = (replaceAt S (e i) z) ∘ e :=
  (Function.update_comp_eq_of_injective S e.injective i z).symm
include hf hb in
lemma replacement_invariant {m : ℕ} (i k : Fin m) :
    (∫ p : (Fin m → Z) × Z,
      |f (trainingSet p.1) (p.1 i) - f (trainingSet (replaceAt p.1 i p.2)) (p.1 i)|
      ∂((Measure.pi fun _ : Fin m => D).prod D)) =
    ∫ p : (Fin m → Z) × Z,
      |f (trainingSet p.1) (p.1 k) - f (trainingSet (replaceAt p.1 k p.2)) (p.1 k)|
      ∂((Measure.pi fun _ : Fin m => D).prod D) := by
  rw [replacement_prod D f hf M hb i,replacement_prod D f hf M hb k]
  have h := StabMoments.integral_permutation D (Equiv.swap i k)
    (fun S => ∫ z, |f (trainingSet S) (S i) - f (trainingSet (replaceAt S i z)) (S i)| ∂D)
  simpa only [replace_permutation,StabMoments.training_permutation,Function.comp_apply,Equiv.swap_apply_left] using h.symm
lemma replace_cons {n : ℕ} (a z : Z) (R : Fin n → Z) :
    replaceAt (Fin.cons a R) 0 z = Fin.cons z R := by
  classical
  ext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [replaceAt]
include hf hb in
lemma replacement_identification (n : ℕ) :
    (∫ p : (Fin (n+2) → Z) × Z,
      |f (trainingSet p.1) (p.1 0) - f (trainingSet (replaceAt p.1 0 p.2)) (p.1 0)|
      ∂((Measure.pi fun _ : Fin (n+2) => D).prod D)) =
    ∫ R, StabCross.d D (fun a b z => f (a ::ₘ b ::ₘ trainingSet R) z) 0 1 0 2 1 0
      ∂(Measure.pi fun _ : Fin n => D) := by
  rw [replacement_prod D f hf M hb,
    StabCross.integral_cons_two D _ (replacement_average_measurable D f hf 0) |M|
      (replacement_average_bound D f M hb 0)]
  apply integral_congr_ae
  filter_upwards [] with R
  rw [StabCross.d_replacement D _ (StabCross.two_point_measurable f hf R) M (fun a b z => hb _ _)]
  simp only [replace_cons,StabCross.training_cons,Fin.cons_zero]
end StabFull

set_option backward.isDefEq.respectTransparency false
open MeasureTheory StabGen.Hypothesis
namespace StabFull
variable {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (f : Multiset Z → Z → ℝ)
    (hf : ∀ n, Measurable (fun p : (Fin n → Z) × Z => f (trainingSet p.1) p.2))
    (M : ℝ) (hb : ∀ T z, 0 ≤ f T z ∧ f T z ≤ M)
include hf hb in
lemma sample_cross_bound (n : ℕ) :
    (∫ S, (∫ z, f (trainingSet S) z ∂D)^2 ∂(Measure.pi fun _ : Fin (n+2) => D)) +
    (∫ S, f (trainingSet S) (S 0) * f (trainingSet S) (S 1)
      ∂(Measure.pi fun _ : Fin (n+2) => D)) -
    2*(∫ S, (∫ z, f (trainingSet S) z ∂D) * f (trainingSet S) (S 0)
      ∂(Measure.pi fun _ : Fin (n+2) => D)) ≤
    3*M*(∫ p : (Fin (n+2) → Z) × Z,
      |f (trainingSet p.1) (p.1 0) - f (trainingSet (replaceAt p.1 0 p.2)) (p.1 0)|
      ∂((Measure.pi fun _ : Fin (n+2) => D).prod D)) := by
  rw [fresh_identification D f hf M hb n,training_identification D f hf M hb n,
    mixed_identification D f hf M hb n,replacement_identification D f hf M hb n]
  exact StabCross.random_training_cross D f hf M hb n
include hf hb in
lemma diagonal_gap {m : ℕ} (i j : Fin m) :
    M*(∫ S,f (trainingSet S) (S i) ∂(Measure.pi fun _ : Fin m => D)) -
    (∫ S,f (trainingSet S) (S i)*f (trainingSet S) (S j)
      ∂(Measure.pi fun _ : Fin m => D)) ≤ M^2/2 := by
  have h := StabDiagonal.training_pair D f (hf m) M hb i j
  have he : (fun S : Fin m → Z => f (trainingSet S) (S i) * (M-f (trainingSet S) (S j))) =
      (fun S => M*f (trainingSet S) (S i) - f (trainingSet S) (S i)*f (trainingSet S) (S j)) := by
    funext S; ring
  rw [he,integral_sub ((StabMoments.loss_integrable D f (hf m) M hb i).const_mul M)
    (StabMoments.loss_product_integrable D f (hf m) M hb i j),integral_const_mul] at h
  exact h
include hf hb in
theorem empirical_bound_two (n : ℕ) (i : Fin (n+2)) :
    (∫ S, ((∫ z, f (trainingSet S) z ∂D) - StabMoments.emp f S)^2
      ∂(Measure.pi fun _ : Fin (n+2) => D)) ≤
      M^2/(2*((n+2:ℕ):ℝ)) + 3*M*(∫ p : (Fin (n+2) → Z) × Z,
        |f (trainingSet p.1) (p.1 i) - f (trainingSet (replaceAt p.1 i p.2)) (p.1 i)|
        ∂((Measure.pi fun _ : Fin (n+2) => D).prod D)) := by
  have hne : (0 : Fin (n+2)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  have hd := StabMoments.deviation_bound D f (hf (n+2)) M hb (by omega : 0<n+2) 0 1 hne
  rw [StabMoments.fresh_square D f (hf (n+2)) M hb,
    StabMoments.fresh_mixed D f (hf (n+2)) M hb] at hd
  have hc := sample_cross_bound D f hf M hb n
  rw [replacement_invariant D f hf M hb 0 i] at hc
  have hg := diagonal_gap D f hf M hb (0 : Fin (n+2)) 1
  have hg' := mul_le_mul_of_nonneg_left hg (show 0 ≤ 1 / ((n+2 : ℕ) : ℝ) by positivity)
  have hscale : (1/((n+2:ℕ):ℝ))*(M^2/2) = M^2/(2*((n+2:ℕ):ℝ)) := by ring
  rw [hscale] at hg'
  have hform (a b : ℝ) : (1/((n+2:ℕ):ℝ))*(M*a-b) = M/((n+2:ℕ):ℝ)*a - 1/((n+2:ℕ):ℝ)*b := by ring
  rw [hform] at hg'
  linarith only [hd,hc,hg']
include hf hb in
theorem empirical_bound (m : ℕ) (hm : 2 ≤ m) (i : Fin m) :
    (∫ S, ((∫ z, f (trainingSet S) z ∂D) - StabMoments.emp f S)^2
      ∂(Measure.pi fun _ : Fin m => D)) ≤
      M^2/(2*(m:ℝ)) + 3*M*(∫ p : (Fin m → Z) × Z,
        |f (trainingSet p.1) (p.1 i) - f (trainingSet (replaceAt p.1 i p.2)) (p.1 i)|
        ∂((Measure.pi fun _ : Fin m => D).prod D)) := by
  obtain ⟨n,rfl⟩ : ∃ n, m = n+2 := ⟨m-2,by omega⟩
  exact empirical_bound_two D f hf M hb n i
end StabFull

open FoundationsML.Stability in
theorem empirical_solution {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ) (M : ℝ)
    (hL : ∀ (y' : Y') (y : Y), 0 ≤ L y' y ∧ L y' y ≤ M)
    (A : LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable (fun p : (Fin n → X × Y) × (X × Y) =>
      Loss L (A (trainingSet p.1)) p.2))
    (m : ℕ) (hm : 2 ≤ m) (i : Fin m) :
    ∫ S : Fin m → X × Y,
        (GeneralizationError D L (A (trainingSet S)) - EmpiricalError L S (A (trainingSet S))) ^ 2
      ∂(Measure.pi fun _ : Fin m => D)
    ≤ M ^ 2 / (2 * (m : ℝ))
      + 3 * M * ∫ p : (Fin m → X × Y) × (X × Y),
          |Loss L (A (trainingSet p.1)) (p.1 i)
            - Loss L (A (trainingSet (replaceAt p.1 i p.2))) (p.1 i)|
        ∂((Measure.pi fun _ : Fin m => D).prod D) := by
  simpa only [GeneralizationError,EmpiricalError,StabMoments.emp] using
    StabFull.empirical_bound D (fun T z => Loss L (A T) z) hA M (fun T z => hL (A T z.1) z.2) m hm i
#print axioms empirical_solution

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
    (m : ℕ) (hm : 2 ≤ m) (β₁ β₂ : ℝ) (h₁ : HypothesisStable D L A m β₁)
    (h₂ : PointwiseHypothesisStable D L A m β₂) :
    ∫ S : Fin m → X × Y,
        (GeneralizationError D L (A (trainingSet S)) - EmpiricalError L S (A (trainingSet S))) ^ 2
      ∂(Measure.pi fun _ : Fin m => D)
    ≤ M ^ 2 / (2 * (m : ℝ)) + 3 * M * (β₁ + β₂) := by
  let f : Multiset (X × Y) → (X × Y) → ℝ := fun T z => Loss L (A T) z
  have hb (T : Multiset (X × Y)) (z : X × Y) : 0 ≤ f T z ∧ f T z ≤ M := hL _ _
  have hM : 0 ≤ M := by
    have h := StabMoments.risk_bounds D f (hA 0) M hb (Fin.elim0 : Fin 0 → X × Y)
    exact h.1.trans h.2
  let i : Fin m := ⟨0,by omega⟩
  have hbase := StabFull.empirical_bound D f hA M hb m hm i
  have hrep := ReplaceStability.replace_bound D f hA M hb i β₁ β₂ (h₁ i).2 (h₂ i).2
  have h := hbase.trans (add_le_add (le_refl (M^2/(2*(m:ℝ)))) (mul_le_mul_of_nonneg_left hrep
    (mul_nonneg (by norm_num : (0:ℝ)≤3) hM)))
  simpa only [f,GeneralizationError,EmpiricalError,StabMoments.emp] using h
#print axioms solution

end EmpiricalPrior

namespace LooPrior
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
namespace StabDiagonal
lemma pair_gap (a b M : ℝ) (ha : 0 ≤ a ∧ a ≤ M) (hb : 0 ≤ b ∧ b ≤ M) :
    a * (M-b) ≤ M^2/2 + (M/2)*(a-b) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2),mul_nonneg ha.1 hb.1]
lemma equal_mean_pair {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (a b : Ω → ℝ) (ha : Measurable a) (hb : Measurable b) (M : ℝ)
    (ba : ∀ x, 0 ≤ a x ∧ a x ≤ M) (bb : ∀ x, 0 ≤ b x ∧ b x ≤ M)
    (he : (∫ x, a x ∂μ) = ∫ x, b x ∂μ) :
    (∫ x, a x * (M-b x) ∂μ) ≤ M^2/2 := by
  have ba' (x : Ω) : |a x| ≤ |M| := by rw [abs_of_nonneg (ba x).1]; exact (ba x).2.trans (le_abs_self M)
  have bb' (x : Ω) : |b x| ≤ |M| := by rw [abs_of_nonneg (bb x).1]; exact (bb x).2.trans (le_abs_self M)
  have bc' (x : Ω) : |M-b x| ≤ |M| := by
    rw [abs_of_nonneg (sub_nonneg.mpr (bb x).2)]
    exact (sub_le_self M (bb x).1).trans (le_abs_self M)
  have ia := StabMoments.bounded_integrable μ ha |M| ba'
  have ib := StabMoments.bounded_integrable μ hb |M| bb'
  have iac := StabMoments.bounded_product μ ha (measurable_const.sub hb) |M| ba' bc'
  calc
    _ ≤ ∫ x, (M^2/2 + (M/2)*(a x-b x)) ∂μ :=
      integral_mono iac ((integrable_const _).add ((ia.sub ib).const_mul (M/2)))
        (fun x => pair_gap _ _ _ (ba x) (bb x))
    _ = M^2/2 := by
      change (∫ x, (M^2/2 + (M/2)*((a-b) x)) ∂μ) = _
      rw [integral_add (integrable_const _) ((ia.sub ib).const_mul (M/2)),
        integral_const_mul]
      simp only [Pi.sub_apply]
      rw [integral_sub ia ib,he]
      simp
lemma training_pair {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    {m : ℕ} (f : Multiset Z → Z → ℝ)
    (hf : Measurable (fun p : (Fin m → Z) × Z => f (StabGen.Hypothesis.trainingSet p.1) p.2))
    (M : ℝ) (hb : ∀ T z, 0 ≤ f T z ∧ f T z ≤ M) (i j : Fin m) :
    (∫ S, f (StabGen.Hypothesis.trainingSet S) (S i) *
      (M-f (StabGen.Hypothesis.trainingSet S) (S j)) ∂(Measure.pi fun _ : Fin m => D)) ≤ M^2/2 := by
  apply equal_mean_pair _ _ _ (StabMoments.loss_measurable f hf i)
    (StabMoments.loss_measurable f hf j) M (fun S => hb _ _) (fun S => hb _ _)
  exact StabMoments.diagonal_invariant D f i j id
#print axioms training_pair
end StabDiagonal

set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace LooCross
structure Kernel (Z : Type*) where
  value : Fin 4 → Fin 4 → Fin 4 → (Fin 4 → Z) → ℝ
  perm : ∀ (e : Equiv.Perm (Fin 4)) i j k S,
    value (e i) (e j) (e k) S = value i j k (S ∘ e)
instance {Z : Type*} : CoeFun (Kernel Z) (fun _ => Fin 4 → Fin 4 → Fin 4 → (Fin 4 → Z) → ℝ) := ⟨Kernel.value⟩
variable {Z : Type*} [MeasurableSpace Z]
noncomputable def ell (F : Kernel Z) (i j k : Fin 4) (S : Fin 4 → Z) : ℝ :=
  F i j k S
noncomputable def q (D : Measure Z) (F : Kernel Z) (i j k a b c : Fin 4) : ℝ :=
  ∫ S, ell F i j k S * ell F a b c S ∂(Measure.pi fun _ : Fin 4 => D)
lemma q_perm (D : Measure Z) [IsProbabilityMeasure D] (F : Kernel Z)
    (e : Equiv.Perm (Fin 4)) (i j k a b c : Fin 4) :
    q D F (e i) (e j) (e k) (e a) (e b) (e c) = q D F i j k a b c := by
  simpa only [q, ell, F.perm] using StabMoments.integral_permutation D e (fun S => ell F i j k S * ell F a b c S)
lemma q_swap_left (D : Measure Z) (F : Kernel Z)
    (hs : ∀ a b z, F a b z = F b a z) (i j k a b c : Fin 4) :
    q D F i j k a b c = q D F j i k a b c := by
  unfold q
  apply integral_congr_ae
  filter_upwards [] with S
  change F i j k S * _ = F j i k S * _
  rw [hs i j k]
lemma q_comm (D : Measure Z) (F : Kernel Z) (i j k a b c : Fin 4) :
    q D F i j k a b c = q D F a b c i j k := by
  unfold q
  simp only [mul_comm]
noncomputable def d (D : Measure Z) (F : Kernel Z) (i j k a b c : Fin 4) : ℝ :=
  ∫ S, |ell F i j k S - ell F a b c S| ∂(Measure.pi fun _ : Fin 4 => D)
lemma d_perm (D : Measure Z) [IsProbabilityMeasure D] (F : Kernel Z)
    (e : Equiv.Perm (Fin 4)) (i j k a b c : Fin 4) :
    d D F (e i) (e j) (e k) (e a) (e b) (e c) = d D F i j k a b c := by
  simpa only [d, ell, F.perm] using StabMoments.integral_permutation D e (fun S => |ell F i j k S - ell F a b c S|)
lemma d_swap_left (D : Measure Z) (F : Kernel Z)
    (hs : ∀ a b z, F a b z = F b a z) (i j k a b c : Fin 4) :
    d D F i j k a b c = d D F j i k a b c := by
  unfold d
  apply integral_congr_ae
  filter_upwards [] with S
  change |F i j k S - _| = |F j i k S - _|
  rw [hs i j k]
lemma d_comm (D : Measure Z) (F : Kernel Z) (i j k a b c : Fin 4) :
    d D F i j k a b c = d D F a b c i j k := by
  unfold d
  simp only [abs_sub_comm]
variable (D : Measure Z) [IsProbabilityMeasure D] (F : Kernel Z)
    (hf : ∀ i j k, Measurable (ell F i j k))
    (M : ℝ) (hb : ∀ a b z S, 0 ≤ F a b z S ∧ F a b z S ≤ M)
include hf in
lemma ell_measurable (i j k : Fin 4) : Measurable (ell F i j k) := by
  exact hf i j k
include hb in
lemma ell_bound (i j k : Fin 4) (S : Fin 4 → Z) : |ell F i j k S| ≤ |M| := by
  rw [ell,abs_of_nonneg (hb _ _ _ _).1]
  exact (hb _ _ _ _).2.trans (le_abs_self M)
include hf hb in
lemma pair_integrable (i j k a b c : Fin 4) :
    Integrable (fun S => ell F i j k S * ell F a b c S) (Measure.pi fun _ : Fin 4 => D) :=
  StabMoments.bounded_product _ (ell_measurable F hf i j k) (ell_measurable F hf a b c) |M|
    (ell_bound F M hb i j k) (ell_bound F M hb a b c)
end LooCross

open MeasureTheory
namespace LooCross
variable {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (F : Kernel Z) (hs : ∀ a b z, F a b z = F b a z)
include hs in
lemma q_012013 : q D F 0 1 2 0 1 3 = q D F 0 1 2 0 1 3 := by
  rfl
include hs in
lemma q_012201 : q D F 0 1 2 2 0 1 = q D F 0 1 2 0 2 1 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![0,1,2,3] : Fin 4 → Fin 4) (by decide)
  calc
    q D F 0 1 2 2 0 1 = q D F 0 1 2 2 0 1 := by
      simpa [e] using (q_perm D F e 0 1 2 2 0 1).symm
    _ = q D F 2 0 1 0 1 2 := q_comm D F 0 1 2 2 0 1
    _ = q D F 0 2 1 0 1 2 := q_swap_left D F hs 2 0 1 0 1 2
    _ = q D F 0 1 2 0 2 1 := q_comm D F 0 2 1 0 1 2
include hs in
lemma q_212013 : q D F 2 1 2 0 1 3 = q D F 0 1 0 1 2 3 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![2,1,0,3] : Fin 4 → Fin 4) (by decide)
  calc
    q D F 2 1 2 0 1 3 = q D F 0 1 0 2 1 3 := by
      simpa [e] using (q_perm D F e 2 1 2 0 1 3).symm
    _ = q D F 2 1 3 0 1 0 := q_comm D F 0 1 0 2 1 3
    _ = q D F 1 2 3 0 1 0 := q_swap_left D F hs 2 1 3 0 1 0
    _ = q D F 0 1 0 1 2 3 := q_comm D F 1 2 3 0 1 0
include hs in
lemma q_212201 : q D F 2 1 2 2 0 1 = q D F 0 1 0 0 2 1 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![2,1,0,3] : Fin 4 → Fin 4) (by decide)
  calc
    q D F 2 1 2 2 0 1 = q D F 0 1 0 0 2 1 := by
      simpa [e] using (q_perm D F e 2 1 2 2 0 1).symm
include hs in
lemma q_212123 : q D F 2 1 2 1 2 3 = q D F 0 1 0 0 1 2 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![3,1,0,2] : Fin 4 → Fin 4) (by decide)
  calc
    q D F 2 1 2 1 2 3 = q D F 0 1 0 1 0 2 := by
      simpa [e] using (q_perm D F e 2 1 2 1 2 3).symm
    _ = q D F 1 0 2 0 1 0 := q_comm D F 0 1 0 1 0 2
    _ = q D F 0 1 2 0 1 0 := q_swap_left D F hs 1 0 2 0 1 0
    _ = q D F 0 1 0 0 1 2 := q_comm D F 0 1 2 0 1 0
include hs in
lemma q_132013 : q D F 1 3 2 0 1 3 = q D F 0 1 2 0 2 3 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![1,0,3,2] : Fin 4 → Fin 4) (by decide)
  calc
    q D F 1 3 2 0 1 3 = q D F 0 2 3 1 0 2 := by
      simpa [e] using (q_perm D F e 1 3 2 0 1 3).symm
    _ = q D F 1 0 2 0 2 3 := q_comm D F 0 2 3 1 0 2
    _ = q D F 0 1 2 0 2 3 := q_swap_left D F hs 1 0 2 0 2 3
    _ = q D F 0 2 3 0 1 2 := q_comm D F 0 1 2 0 2 3
    _ = q D F 0 1 2 0 2 3 := q_comm D F 0 2 3 0 1 2
include hs in
lemma q_132123 : q D F 1 3 2 1 2 3 = q D F 0 1 2 0 2 1 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![3,0,1,2] : Fin 4 → Fin 4) (by decide)
  calc
    q D F 1 3 2 1 2 3 = q D F 0 2 1 0 1 2 := by
      simpa [e] using (q_perm D F e 1 3 2 1 2 3).symm
    _ = q D F 0 1 2 0 2 1 := q_comm D F 0 2 1 0 1 2
include hs in
lemma q_013132 : q D F 0 1 3 1 3 2 = q D F 0 1 2 0 2 3 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![1,0,3,2] : Fin 4 → Fin 4) (by decide)
  calc
    q D F 0 1 3 1 3 2 = q D F 1 0 2 0 2 3 := by
      simpa [e] using (q_perm D F e 0 1 3 1 3 2).symm
    _ = q D F 0 1 2 0 2 3 := q_swap_left D F hs 1 0 2 0 2 3
include hs in
lemma q_013131 : q D F 0 1 3 1 3 1 = q D F 0 1 0 0 2 1 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![2,0,3,1] : Fin 4 → Fin 4) (by decide)
  calc
    q D F 0 1 3 1 3 1 = q D F 2 0 1 0 1 0 := by
      simpa [e] using (q_perm D F e 0 1 3 1 3 1).symm
    _ = q D F 0 2 1 0 1 0 := q_swap_left D F hs 2 0 1 0 1 0
    _ = q D F 0 1 0 0 2 1 := q_comm D F 0 2 1 0 1 0
include hs in
lemma q_133132 : q D F 1 3 3 1 3 2 = q D F 0 1 0 0 1 2 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![3,1,2,0] : Fin 4 → Fin 4) (by decide)
  calc
    q D F 1 3 3 1 3 2 = q D F 1 0 0 1 0 2 := by
      simpa [e] using (q_perm D F e 1 3 3 1 3 2).symm
    _ = q D F 0 1 0 1 0 2 := q_swap_left D F hs 1 0 0 1 0 2
    _ = q D F 1 0 2 0 1 0 := q_comm D F 0 1 0 1 0 2
    _ = q D F 0 1 2 0 1 0 := q_swap_left D F hs 1 0 2 0 1 0
    _ = q D F 0 1 0 0 1 2 := q_comm D F 0 1 2 0 1 0
include hs in
lemma q_133131 : q D F 1 3 3 1 3 1 = q D F 0 1 0 0 1 1 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![2,0,3,1] : Fin 4 → Fin 4) (by decide)
  calc
    q D F 1 3 3 1 3 1 = q D F 0 1 1 0 1 0 := by
      simpa [e] using (q_perm D F e 1 3 3 1 3 1).symm
    _ = q D F 0 1 0 0 1 1 := q_comm D F 0 1 1 0 1 0
include hs in
lemma q_010011 : q D F 0 1 0 0 1 1 = q D F 0 1 0 0 1 1 := by
  rfl
include hs in
lemma q_012010 : q D F 0 1 2 0 1 0 = q D F 0 1 0 0 1 2 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![0,1,2,3] : Fin 4 → Fin 4) (by decide)
  calc
    q D F 0 1 2 0 1 0 = q D F 0 1 2 0 1 0 := by
      simpa [e] using (q_perm D F e 0 1 2 0 1 0).symm
    _ = q D F 0 1 0 0 1 2 := q_comm D F 0 1 2 0 1 0
include hs in
lemma d_012212 : d D F 0 1 2 2 1 2 = d D F 0 1 0 1 2 0 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![2,1,0,3] : Fin 4 → Fin 4) (by decide)
  calc
    d D F 0 1 2 2 1 2 = d D F 2 1 0 0 1 0 := by
      simpa [e] using (d_perm D F e 0 1 2 2 1 2).symm
    _ = d D F 1 2 0 0 1 0 := d_swap_left D F hs 2 1 0 0 1 0
    _ = d D F 0 1 0 1 2 0 := d_comm D F 1 2 0 0 1 0
include hs in
lemma d_212132 : d D F 2 1 2 1 3 2 = d D F 0 1 0 1 2 0 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![3,1,0,2] : Fin 4 → Fin 4) (by decide)
  calc
    d D F 2 1 2 1 3 2 = d D F 0 1 0 1 2 0 := by
      simpa [e] using (d_perm D F e 2 1 2 1 3 2).symm
include hs in
lemma d_013133 : d D F 0 1 3 1 3 3 = d D F 0 1 0 1 2 0 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![2,1,3,0] : Fin 4 → Fin 4) (by decide)
  calc
    d D F 0 1 3 1 3 3 = d D F 2 1 0 1 0 0 := by
      simpa [e] using (d_perm D F e 0 1 3 1 3 3).symm
    _ = d D F 1 2 0 1 0 0 := d_swap_left D F hs 2 1 0 1 0 0
    _ = d D F 1 0 0 1 2 0 := d_comm D F 1 2 0 1 0 0
    _ = d D F 0 1 0 1 2 0 := d_swap_left D F hs 1 0 0 1 2 0
    _ = d D F 1 2 0 0 1 0 := d_comm D F 0 1 0 1 2 0
    _ = d D F 0 1 0 1 2 0 := d_comm D F 1 2 0 0 1 0
include hs in
lemma d_010210 : d D F 0 1 0 2 1 0 = d D F 0 1 0 1 2 0 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![0,1,2,3] : Fin 4 → Fin 4) (by decide)
  calc
    d D F 0 1 0 2 1 0 = d D F 0 1 0 2 1 0 := by
      simpa [e] using (d_perm D F e 0 1 0 2 1 0).symm
    _ = d D F 2 1 0 0 1 0 := d_comm D F 0 1 0 2 1 0
    _ = d D F 1 2 0 0 1 0 := d_swap_left D F hs 2 1 0 0 1 0
    _ = d D F 0 1 0 1 2 0 := d_comm D F 1 2 0 0 1 0
include hs in
lemma cancellation :
    (q D F 0 1 2 0 1 3 - q D F 0 1 2 2 0 1 - q D F 2 1 2 0 1 3 + q D F 2 1 2 2 0 1) +
    (q D F 2 1 2 0 1 3 - q D F 2 1 2 1 2 3 - q D F 1 3 2 0 1 3 + q D F 1 3 2 1 2 3) +
    (q D F 0 1 3 1 3 2 - q D F 0 1 3 1 3 1 - q D F 1 3 3 1 3 2 + q D F 1 3 3 1 3 1) =
    q D F 0 1 2 0 1 3 + q D F 0 1 0 0 1 1 - 2 * q D F 0 1 2 0 1 0 := by
  rw [q_012201 D F hs, q_212013 D F hs, q_212201 D F hs, q_212123 D F hs, q_132013 D F hs, q_132123 D F hs, q_013132 D F hs, q_013131 D F hs, q_133132 D F hs, q_133131 D F hs, q_012010 D F hs]
  ring
end LooCross

set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace LooCross
variable {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (F : Kernel Z)
    (hf : ∀ i j k, Measurable (ell F i j k))
    (M : ℝ) (hb : ∀ a b z S, 0 ≤ F a b z S ∧ F a b z S ≤ M)
noncomputable def dd (a b c d e f g h i j k l : Fin 4) : ℝ :=
  ∫ S, (ell F a b c S - ell F d e f S) * (ell F g h i S - ell F j k l S)
    ∂(Measure.pi fun _ : Fin 4 => D)
include hf hb in
lemma dd_expand (a b c d e f g h i j k l : Fin 4) :
    dd D F a b c d e f g h i j k l =
      q D F a b c g h i - q D F a b c j k l - q D F d e f g h i + q D F d e f j k l := by
  have h1 := pair_integrable D F hf M hb a b c g h i
  have h2 := pair_integrable D F hf M hb a b c j k l
  have h3 := pair_integrable D F hf M hb d e f g h i
  have h4 := pair_integrable D F hf M hb d e f j k l
  unfold dd
  simp_rw [sub_mul,mul_sub]
  have he := integral_sub (h1.sub h2) (h3.sub h4)
  dsimp only [Pi.sub_apply] at he
  rw [he,integral_sub h1 h2,integral_sub h3 h4]
  change q D F a b c g h i - q D F a b c j k l -
    (q D F d e f g h i - q D F d e f j k l) = _
  ring
include hb in
lemma ell_diff_bound (a b c d e f : Fin 4) (S : Fin 4 → Z) :
    |ell F a b c S - ell F d e f S| ≤ |M| := by
  have h1 := hb a b c S
  have h2 := hb d e f S
  apply le_trans (show |ell F a b c S - ell F d e f S| ≤ M from ?_) (le_abs_self M)
  apply abs_le.mpr
  dsimp [ell]
  constructor <;> linarith
include hf hb in
lemma dd_bound (a b c d e f g h i j k l : Fin 4) :
    dd D F a b c d e f g h i j k l ≤ M * LooCross.d D F a b c d e f := by
  have hp := StabMoments.bounded_product (Measure.pi fun _ : Fin 4 => D)
    ((ell_measurable F hf a b c).sub (ell_measurable F hf d e f))
    ((ell_measurable F hf g h i).sub (ell_measurable F hf j k l)) |M|
    (ell_diff_bound F M hb a b c d e f) (ell_diff_bound F M hb g h i j k l)
  have ha := StabMoments.bounded_integrable (Measure.pi fun _ : Fin 4 => D)
    ((ell_measurable F hf a b c).sub (ell_measurable F hf d e f)).abs |M|
    (fun S => by simpa only [abs_abs,Pi.sub_apply] using ell_diff_bound F M hb a b c d e f S)
  unfold dd LooCross.d
  rw [← integral_const_mul]
  apply integral_mono hp (ha.const_mul M)
  intro S
  have h1 := hb g h i S
  have h2 := hb j k l S
  have hh : |ell F g h i S - ell F j k l S| ≤ M := by
    apply abs_le.mpr
    dsimp [ell]
    constructor <;> linarith
  calc
    _ ≤ |(ell F a b c S - ell F d e f S) * (ell F g h i S - ell F j k l S)| := le_abs_self _
    _ = |ell F a b c S - ell F d e f S| * |ell F g h i S - ell F j k l S| := abs_mul _ _
    _ ≤ |ell F a b c S - ell F d e f S| * M := mul_le_mul_of_nonneg_left hh (abs_nonneg _)
    _ = _ := mul_comm _ _
include hf hb in
lemma cross_bound (hs : ∀ a b z, F a b z = F b a z) :
    q D F 0 1 2 0 1 3 + q D F 0 1 0 0 1 1 - 2 * q D F 0 1 2 0 1 0 ≤
      3 * M * d D F 0 1 0 2 1 0 := by
  have he : dd D F 0 1 2 2 1 2 0 1 3 2 0 1 +
      dd D F 2 1 2 1 3 2 0 1 3 1 2 3 + dd D F 0 1 3 1 3 3 1 3 2 1 3 1 =
      q D F 0 1 2 0 1 3 + q D F 0 1 0 0 1 1 - 2*q D F 0 1 2 0 1 0 := by
    rw [dd_expand D F hf M hb,dd_expand D F hf M hb,dd_expand D F hf M hb]
    exact cancellation D F hs
  have h1 := dd_bound D F hf M hb 0 1 2 2 1 2 0 1 3 2 0 1
  have h2 := dd_bound D F hf M hb 2 1 2 1 3 2 0 1 3 1 2 3
  have h3 := dd_bound D F hf M hb 0 1 3 1 3 3 1 3 2 1 3 1
  rw [d_012212 D F hs,← d_010210 D F hs] at h1
  rw [d_212132 D F hs,← d_010210 D F hs] at h2
  rw [d_013133 D F hs,← d_010210 D F hs] at h3
  linarith
#print axioms cross_bound
end LooCross

open MeasureTheory
namespace StabCross
lemma training_cons {Z : Type*} {n : ℕ} (a : Z) (S : Fin n → Z) :
    StabGen.Hypothesis.trainingSet (Fin.cons a S) = a ::ₘ StabGen.Hypothesis.trainingSet S := by
  classical
  unfold StabGen.Hypothesis.trainingSet
  rw [Fin.univ_succ]
  simp [Finset.map_val,Multiset.map_map,Function.comp_def]
variable {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
lemma integral_cons {n : ℕ} (g : (Fin (n+1) → Z) → ℝ) (hg : Measurable g)
    (C : ℝ) (hb : ∀ S, |g S| ≤ C) :
    (∫ S, g S ∂(Measure.pi fun _ : Fin (n+1) => D)) =
      ∫ R, ∫ a, g (Fin.cons a R) ∂D ∂(Measure.pi fun _ : Fin n => D) := by
  have hm : Measurable (fun p : Z × (Fin n → Z) => Fin.cons (α := fun _ : Fin (n+1) => Z) p.1 p.2) := by
    apply measurable_pi_lambda
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using (measurable_fst : Measurable (fun p : Z × (Fin n → Z) => p.1))
    · simpa [Function.comp_def] using (measurable_pi_apply j).comp (measurable_snd : Measurable (fun p : Z × (Fin n → Z) => p.2))
  have hi := StabMoments.bounded_integrable (D.prod (Measure.pi fun _ : Fin n => D)) (hg.comp hm) C (fun p => hb _)
  have he := ((measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => D) 0).symm).integral_comp' g
  have hh : (∫ p : Z × (Fin n → Z),g (Fin.cons p.1 p.2) ∂(D.prod (Measure.pi fun _ => D))) =
      ∫ S,g S ∂(Measure.pi fun _ : Fin (n+1) => D) := by
    simpa [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Fin.insertNth_zero] using he
  rw [← hh]
  simpa only [Function.comp_apply] using integral_prod_symm _ hi
lemma integrate_first_measurable {n : ℕ} (g : (Fin (n+1) → Z) → ℝ) (hg : Measurable g) :
    Measurable (fun R : Fin n → Z => ∫ a, g (Fin.cons a R) ∂D) := by
  have hm : Measurable (fun p : (Fin n → Z) × Z => g (Fin.cons p.2 p.1)) := by
    apply hg.comp
    apply measurable_pi_lambda
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using (measurable_snd : Measurable (fun p : (Fin n → Z) × Z => p.2))
    · simpa [Function.comp_def] using (measurable_pi_apply j).comp (measurable_fst : Measurable (fun p : (Fin n → Z) × Z => p.1))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable
lemma integrate_first_bound {n : ℕ} (g : (Fin (n+1) → Z) → ℝ) (C : ℝ)
    (hb : ∀ S, |g S| ≤ C) (R : Fin n → Z) : |∫ a,g (Fin.cons a R) ∂D| ≤ C := by
  calc
    _ ≤ ∫ a, |g (Fin.cons a R)| ∂D := abs_integral_le_integral_abs
    _ ≤ ∫ _ : Z,C ∂D := integral_mono_of_nonneg (Filter.Eventually.of_forall fun a => abs_nonneg _)
      (integrable_const C) (Filter.Eventually.of_forall fun a => hb _)
    _ = C := by simp
lemma integral_four (g : (Fin 4 → Z) → ℝ) (hg : Measurable g) (C : ℝ) (hb : ∀ S, |g S| ≤ C) :
    (∫ S,g S ∂(Measure.pi fun _ : Fin 4 => D)) =
      ∫ d, ∫ c, ∫ b, ∫ a, g ![a,b,c,d] ∂D ∂D ∂D ∂D := by
  rw [integral_cons D g hg C hb]
  rw [integral_cons D _ (integrate_first_measurable D g hg) C (integrate_first_bound D g C hb)]
  rw [integral_cons D _ (integrate_first_measurable D _ (integrate_first_measurable D g hg)) C
    (integrate_first_bound D _ C (integrate_first_bound D g C hb))]
  rw [integral_cons D _ (integrate_first_measurable D _ (integrate_first_measurable D _ (integrate_first_measurable D g hg))) C
    (integrate_first_bound D _ C (integrate_first_bound D _ C (integrate_first_bound D g C hb)))]
  have he (S : Fin 0 → Z) (a b c d : Z) :
      Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d S))) = ![a,b,c,d] := by
    funext i
    fin_cases i <;> rfl
  simp_rw [he]
  simp
lemma integral_four_bacd (g : (Fin 4 → Z) → ℝ) (hg : Measurable g) (C : ℝ) (hb : ∀ S, |g S| ≤ C) :
    (∫ S,g S ∂(Measure.pi fun _ : Fin 4 => D)) =
      ∫ b, ∫ a, ∫ c, ∫ d, g ![a,b,c,d] ∂D ∂D ∂D ∂D := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective (![2,3,1,0] : Fin 4 → Fin 4) (by decide)
  rw [← StabMoments.integral_permutation D e g]
  have hm : Measurable (fun S : Fin 4 → Z => g (S ∘ e)) := hg.comp (by fun_prop)
  rw [integral_four D _ hm C (fun S => hb _)]
  have he (a b c d : Z) : ![a,b,c,d] ∘ e = ![c,d,b,a] := by
    funext i
    fin_cases i <;> rfl
  simp_rw [he]
end StabCross

open StabGen.Hypothesis
namespace StabCross
variable {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
lemma integral_cons_two {n : ℕ} (g : (Fin (n+2) → Z) → ℝ) (hg : Measurable g)
    (C : ℝ) (hb : ∀ S, |g S| ≤ C) :
    (∫ S, g S ∂(Measure.pi fun _ : Fin (n+2) => D)) =
      ∫ R, ∫ b, ∫ a, g (Fin.cons a (Fin.cons b R)) ∂D ∂D ∂(Measure.pi fun _ : Fin n => D) := by
  rw [integral_cons D g hg C hb]
  rw [integral_cons D _ (integrate_first_measurable D g hg) C (integrate_first_bound D g C hb)]
variable (f : Multiset Z → Z → ℝ)
    (hf : ∀ n, Measurable (fun p : (Fin n → Z) × Z => f (trainingSet p.1) p.2))
    (M : ℝ) (hb : ∀ T z, 0 ≤ f T z ∧ f T z ≤ M)

end StabCross

set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace LooCross
variable {Z : Type*} [MeasurableSpace Z]
noncomputable def deletedKernel (F : Z → Z → Z → ℝ) (G : Z → Z → ℝ) : Kernel Z where
  value i j k S := if k=i then G (S j) (S k) else if k=j then G (S i) (S k) else F (S i) (S j) (S k)
  perm e i j k S := by simp [e.injective.eq_iff,Function.comp_def]
lemma deleted_symmetric (F : Z → Z → Z → ℝ) (G : Z → Z → ℝ)
    (hs : ∀ a b z, F a b z = F b a z) :
    ∀ i j k, deletedKernel F G i j k = deletedKernel F G j i k := by
  intro i j k
  funext S
  change (if k=i then _ else if k=j then _ else _) = (if k=j then _ else if k=i then _ else _)
  by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [hs]
lemma deleted_measurable (F : Z → Z → Z → ℝ) (G : Z → Z → ℝ)
    (hf : Measurable (fun p : Z × Z × Z => F p.1 p.2.1 p.2.2))
    (hg : Measurable (fun p : Z × Z => G p.1 p.2)) (i j k : Fin 4) :
    Measurable (ell (deletedKernel F G) i j k) := by
  unfold ell
  change Measurable (fun S : Fin 4 → Z => if k=i then _ else if k=j then _ else _)
  split_ifs
  · exact hg.comp (show Measurable (fun S : Fin 4 → Z => (S j,S k)) from (measurable_pi_apply j).prodMk (measurable_pi_apply k))
  · exact hg.comp (show Measurable (fun S : Fin 4 → Z => (S i,S k)) from (measurable_pi_apply i).prodMk (measurable_pi_apply k))
  · exact hf.comp (show Measurable (fun S : Fin 4 → Z => (S i,S j,S k)) from (measurable_pi_apply i).prodMk ((measurable_pi_apply j).prodMk (measurable_pi_apply k)))
lemma deleted_bounds (F : Z → Z → Z → ℝ) (G : Z → Z → ℝ) (M : ℝ)
    (hb : ∀ a b z, 0 ≤ F a b z ∧ F a b z ≤ M)
    (hc : ∀ b z, 0 ≤ G b z ∧ G b z ≤ M) (i j k : Fin 4) (S : Fin 4 → Z) :
    0 ≤ deletedKernel F G i j k S ∧ deletedKernel F G i j k S ≤ M := by
  change (0 ≤ (if k=i then G (S j) (S k) else if k=j then G (S i) (S k) else F (S i) (S j) (S k))) ∧ ((if k=i then G (S j) (S k) else if k=j then G (S i) (S k) else F (S i) (S j) (S k)) ≤ M)
  split_ifs <;> first | exact hc _ _ | exact hb _ _ _
variable (D : Measure Z) [IsProbabilityMeasure D]
    (F : Z → Z → Z → ℝ) (G : Z → Z → ℝ)
    (hf : Measurable (fun p : Z × Z × Z => F p.1 p.2.1 p.2.2))
    (hg : Measurable (fun p : Z × Z => G p.1 p.2))
    (M : ℝ) (hb : ∀ a b z, 0 ≤ F a b z ∧ F a b z ≤ M)
    (hc : ∀ b z, 0 ≤ G b z ∧ G b z ≤ M)
include hf hg hb hc in
lemma q_iterated (a b c d e f : Fin 4) : q D (deletedKernel F G) a b c d e f =
    ∫ y, ∫ x, ∫ z, ∫ w,
      ell (deletedKernel F G) a b c ![x,y,z,w] * ell (deletedKernel F G) d e f ![x,y,z,w] ∂D ∂D ∂D ∂D := by
  apply StabCross.integral_four_bacd D _ ((deleted_measurable F G hf hg a b c).mul (deleted_measurable F G hf hg d e f)) (|M| * |M|)
  intro S
  rw [Pi.mul_apply,abs_mul]
  exact mul_le_mul (ell_bound _ M (deleted_bounds F G M hb hc) a b c S)
    (ell_bound _ M (deleted_bounds F G M hb hc) d e f S) (abs_nonneg _) (abs_nonneg _)
include hf hg hb hc in
lemma q_fresh : q D (deletedKernel F G) 0 1 2 0 1 3 =
    ∫ b, ∫ a, (∫ z, F a b z ∂D)^2 ∂D ∂D := by
  rw [q_iterated D F G hf hg M hb hc]
  simp [ell,deletedKernel,integral_const_mul,integral_mul_const,pow_two]
include hf hg hb hc in
lemma q_training : q D (deletedKernel F G) 0 1 0 0 1 1 =
    ∫ b, ∫ a, G b a * G a b ∂D ∂D := by
  rw [q_iterated D F G hf hg M hb hc]
  simp [ell,deletedKernel]
include hf hg hb hc in
lemma q_mixed : q D (deletedKernel F G) 0 1 2 0 1 0 =
    ∫ b, ∫ a, (∫ z, F a b z ∂D) * G b a ∂D ∂D := by
  rw [q_iterated D F G hf hg M hb hc]
  simp [ell,deletedKernel,integral_mul_const]
include hf hg hb hc in
lemma d_deleted : d D (deletedKernel F G) 0 1 2 2 1 2 =
    ∫ b, ∫ a, ∫ z, |F a b z - G b z| ∂D ∂D ∂D := by
  unfold d
  have hm : Measurable (fun S => |ell (deletedKernel F G) 0 1 2 S - ell (deletedKernel F G) 2 1 2 S|) := by
    simpa only [Pi.sub_apply] using ((deleted_measurable F G hf hg 0 1 2).sub (deleted_measurable F G hf hg 2 1 2)).abs
  rw [StabCross.integral_four_bacd D _ hm |M|]
  · simp [ell,deletedKernel]
  · intro S
    simpa only [abs_abs] using ell_diff_bound _ M (deleted_bounds F G M hb hc) 0 1 2 2 1 2 S
#print axioms d_deleted
end LooCross

open MeasureTheory
namespace LooCross
variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : Measure Z) [IsProbabilityMeasure D]
    (F : Ω → Kernel Z)
    (hf : ∀ a b c, Measurable (fun p : Ω × (Fin 4 → Z) => ell (F p.1) a b c p.2))
    (M : ℝ) (hb : ∀ r a b z S, 0 ≤ F r a b z S ∧ F r a b z S ≤ M)
include hf in
lemma context_ell_measurable (a b c : Fin 4) :
    Measurable (fun p : Ω × (Fin 4 → Z) => ell (F p.1) a b c p.2) := by
  exact hf a b c
include hf in
lemma context_q_measurable (a b c d e f : Fin 4) :
    Measurable (fun r => q D (F r) a b c d e f) := by
  exact ((context_ell_measurable F hf a b c).mul (context_ell_measurable F hf d e f)).stronglyMeasurable.integral_prod_right'.measurable
include hf in
lemma context_d_measurable (a b c d e f : Fin 4) :
    Measurable (fun r => LooCross.d D (F r) a b c d e f) := by
  exact ((context_ell_measurable F hf a b c).sub (context_ell_measurable F hf d e f)).abs.stronglyMeasurable.integral_prod_right'.measurable
include hb in
lemma context_q_bound (a b c d e f : Fin 4) (r : Ω) :
    |q D (F r) a b c d e f| ≤ |M| * |M| := by
  unfold q
  calc
    _ ≤ ∫ S, |ell (F r) a b c S * ell (F r) d e f S| ∂(Measure.pi fun _ : Fin 4 => D) := abs_integral_le_integral_abs
    _ ≤ ∫ _S : Fin 4 → Z, |M| * |M| ∂(Measure.pi fun _ : Fin 4 => D) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun S => abs_nonneg _) (integrable_const _)
      filter_upwards [] with S
      rw [abs_mul]
      exact mul_le_mul (ell_bound (F r) M (hb r) a b c S) (ell_bound (F r) M (hb r) d e f S) (abs_nonneg _) (abs_nonneg _)
    _ = _ := by simp
include hb in
lemma context_d_bound (a b c d e f : Fin 4) (r : Ω) :
    |LooCross.d D (F r) a b c d e f| ≤ |M| := by
  unfold LooCross.d
  calc
    _ ≤ ∫ S, |ell (F r) a b c S - ell (F r) d e f S| ∂(Measure.pi fun _ : Fin 4 => D) := by
      simpa only [abs_abs] using (abs_integral_le_integral_abs (f := fun S => |ell (F r) a b c S - ell (F r) d e f S|) (μ := Measure.pi fun _ : Fin 4 => D))
    _ ≤ ∫ _S : Fin 4 → Z, |M| ∂(Measure.pi fun _ : Fin 4 => D) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun S => abs_nonneg _) (integrable_const _)
      exact Filter.Eventually.of_forall (ell_diff_bound (F r) M (hb r) a b c d e f)
    _ = _ := by simp
include hf hb in
lemma random_context_cross (hs : ∀ r a b z, F r a b z = F r b a z) :
    (∫ r, q D (F r) 0 1 2 0 1 3 ∂μ) + (∫ r, q D (F r) 0 1 0 0 1 1 ∂μ) -
    2*(∫ r,q D (F r) 0 1 2 0 1 0 ∂μ) ≤ 3*M*(∫ r,LooCross.d D (F r) 0 1 0 2 1 0 ∂μ) := by
  have hi (a b c d e f : Fin 4) := StabMoments.bounded_integrable μ
    (context_q_measurable D F hf a b c d e f) (|M| * |M|) (context_q_bound D F M hb a b c d e f)
  have hd := StabMoments.bounded_integrable μ (context_d_measurable D F hf 0 1 0 2 1 0) |M|
    (context_d_bound D F M hb 0 1 0 2 1 0)
  have hleft := integral_sub ((hi 0 1 2 0 1 3).add (hi 0 1 0 0 1 1)) ((hi 0 1 2 0 1 0).const_mul 2)
  dsimp only [Pi.add_apply] at hleft
  rw [integral_add (hi 0 1 2 0 1 3) (hi 0 1 0 0 1 1),integral_const_mul] at hleft
  rw [← hleft,← integral_const_mul]
  apply integral_mono (((hi 0 1 2 0 1 3).add (hi 0 1 0 0 1 1)).sub ((hi 0 1 2 0 1 0).const_mul 2)) (hd.const_mul (3*M))
  intro r
  have hr (a b c : Fin 4) : Measurable (ell (F r) a b c) :=
    (hf a b c).comp (measurable_const.prodMk measurable_id)
  exact cross_bound D (F r) hr M (hb r) (hs r)
#print axioms random_context_cross
end LooCross

set_option backward.isDefEq.respectTransparency false
open MeasureTheory StabGen.Hypothesis
namespace LooFull
variable {Z : Type*} [MeasurableSpace Z]
lemma cons_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (a : Ω → Z) (s : Ω → Fin n → Z) (ha : Measurable a) (hs : Measurable s) :
    Measurable (fun p => (Fin.cons (a p) (s p) : Fin (n+1) → Z)) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using ha
  · simpa only [Fin.cons_succ,Function.comp_def] using (measurable_pi_apply j).comp hs
noncomputable def trainingKernel {n : ℕ} (f : Multiset Z → Z → ℝ) (R : Fin n → Z) : LooCross.Kernel Z :=
  LooCross.deletedKernel (fun a b z => f (a ::ₘ b ::ₘ trainingSet R) z)
    (fun b z => f (b ::ₘ trainingSet R) z)
variable (f : Multiset Z → Z → ℝ)
    (hf : ∀ n, Measurable (fun p : (Fin n → Z) × Z => f (trainingSet p.1) p.2))
    (M : ℝ) (hb : ∀ T z, 0 ≤ f T z ∧ f T z ≤ M)
include hf in
lemma two_measurable {n : ℕ} (R : Fin n → Z) :
    Measurable (fun p : Z × Z × Z => f (p.1 ::ₘ p.2.1 ::ₘ trainingSet R) p.2.2) := by
  have h := (hf (n+2)).comp ((cons_measurable (fun p : Z × Z × Z => p.1)
    (fun p => Fin.cons p.2.1 R) measurable_fst (cons_measurable _ _ (by fun_prop) measurable_const)).prodMk (show Measurable (fun p : Z × Z × Z => p.2.2) by fun_prop))
  simpa only [Function.comp_def,StabCross.training_cons] using h
include hf in
lemma one_measurable {n : ℕ} (R : Fin n → Z) :
    Measurable (fun p : Z × Z => f (p.1 ::ₘ trainingSet R) p.2) := by
  have h := (hf (n+1)).comp ((cons_measurable (fun p : Z × Z => p.1)
    (fun _ => R) measurable_fst measurable_const).prodMk measurable_snd)
  simpa only [Function.comp_def,StabCross.training_cons] using h
include hf in
lemma context_measurable (n : ℕ) (a b c : Fin 4) :
    Measurable (fun p : (Fin n → Z) × (Fin 4 → Z) =>
      LooCross.ell (trainingKernel f p.1) a b c p.2) := by
  have he (i : Fin 4) : Measurable (fun p : (Fin n → Z) × (Fin 4 → Z) => p.2 i) := by fun_prop
  have ho (i j : Fin 4) : Measurable (fun p : (Fin n → Z) × (Fin 4 → Z) =>
      f (p.2 i ::ₘ trainingSet p.1) (p.2 j)) := by
    have h := (hf (n+1)).comp ((cons_measurable _ _ (he i) measurable_fst).prodMk (he j))
    simpa only [Function.comp_def,StabCross.training_cons] using h
  have ht : Measurable (fun p : (Fin n → Z) × (Fin 4 → Z) =>
      f (p.2 a ::ₘ p.2 b ::ₘ trainingSet p.1) (p.2 c)) := by
    have h := (hf (n+2)).comp ((cons_measurable _ _ (he a)
      (cons_measurable _ _ (he b) measurable_fst)).prodMk (he c))
    simpa only [Function.comp_def,StabCross.training_cons] using h
  change Measurable (fun p : (Fin n → Z) × (Fin 4 → Z) =>
    if c=a then f (p.2 b ::ₘ trainingSet p.1) (p.2 c)
    else if c=b then f (p.2 a ::ₘ trainingSet p.1) (p.2 c)
    else f (p.2 a ::ₘ p.2 b ::ₘ trainingSet p.1) (p.2 c))
  split_ifs <;> first | exact ho _ _ | exact ht
include hb in
lemma kernel_bounds {n : ℕ} (R : Fin n → Z) (a b c : Fin 4) (S : Fin 4 → Z) :
    0 ≤ trainingKernel f R a b c S ∧ trainingKernel f R a b c S ≤ M :=
  LooCross.deleted_bounds _ _ M (fun a b z => hb _ _) (fun b z => hb _ _) a b c S
lemma kernel_symmetric {n : ℕ} (R : Fin n → Z) :
    ∀ a b c, trainingKernel f R a b c = trainingKernel f R b a c := by
  apply LooCross.deleted_symmetric
  intro a b z
  rw [Multiset.cons_swap]
lemma remove_zero {n : ℕ} (a : Z) (R : Fin n → Z) :
    removeAt (Fin.cons a R) 0 = trainingSet R := by
  apply (Multiset.cons_inj_right a).mp
  have h := LooMoments.training_cons_remove (Fin.cons a R) 0
  simpa only [StabCross.training_cons,Fin.cons_zero] using h.symm
lemma remove_one {n : ℕ} (a b : Z) (R : Fin n → Z) :
    removeAt (Fin.cons a (Fin.cons b R)) 1 = a ::ₘ trainingSet R := by
  apply (Multiset.cons_inj_right b).mp
  have h := LooMoments.training_cons_remove (Fin.cons a (Fin.cons b R)) 1
  simpa only [StabCross.training_cons,Fin.cons_one,Fin.cons_zero,Multiset.cons_swap] using h.symm
variable (D : Measure Z) [IsProbabilityMeasure D]
include hf hb in
lemma random_training_cross (n : ℕ) :
    (∫ R, LooCross.q D (trainingKernel f R) 0 1 2 0 1 3 ∂(Measure.pi fun _ : Fin n => D)) +
    (∫ R, LooCross.q D (trainingKernel f R) 0 1 0 0 1 1 ∂(Measure.pi fun _ : Fin n => D)) -
    2*(∫ R,LooCross.q D (trainingKernel f R) 0 1 2 0 1 0 ∂(Measure.pi fun _ : Fin n => D)) ≤
    3*M*(∫ R,LooCross.d D (trainingKernel f R) 0 1 2 2 1 2 ∂(Measure.pi fun _ : Fin n => D)) := by
  have h := LooCross.random_context_cross (Measure.pi fun _ : Fin n => D) D
    (trainingKernel f) (context_measurable f hf n) M (kernel_bounds f M hb) (kernel_symmetric f)
  have he (R : Fin n → Z) : LooCross.d D (trainingKernel f R) 0 1 0 2 1 0 =
      LooCross.d D (trainingKernel f R) 0 1 2 2 1 2 := by
    rw [LooCross.d_010210 D _ (kernel_symmetric f R),LooCross.d_012212 D _ (kernel_symmetric f R)]
  simpa only [he] using h
#print axioms random_training_cross
end LooFull

set_option backward.isDefEq.respectTransparency false
open MeasureTheory StabGen.Hypothesis
namespace LooFull
variable {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (f : Multiset Z → Z → ℝ)
    (hf : ∀ n, Measurable (fun p : (Fin n → Z) × Z => f (trainingSet p.1) p.2))
    (M : ℝ) (hb : ∀ T z, 0 ≤ f T z ∧ f T z ≤ M)
include hf hb in
lemma fresh_identification (n : ℕ) :
    (∫ S, (∫ z, f (trainingSet S) z ∂D)^2 ∂(Measure.pi fun _ : Fin (n+2) => D)) =
    ∫ R, LooCross.q D (trainingKernel f R) 0 1 2 0 1 3
      ∂(Measure.pi fun _ : Fin n => D) := by
  have hB (S : Fin (n+2) → Z) : |(∫ z, f (trainingSet S) z ∂D)^2| ≤ |M|^2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (StabMoments.risk_bound D f (hf _) M hb S) _
  rw [StabCross.integral_cons_two D _ ((StabMoments.risk_measurable D f (hf _)).pow_const 2) (|M|^2) hB]
  apply integral_congr_ae
  filter_upwards [] with R
  unfold trainingKernel
  rw [LooCross.q_fresh D (fun a b z => f (a ::ₘ b ::ₘ trainingSet R) z) (fun b z => f (b ::ₘ trainingSet R) z) (two_measurable f hf R) (one_measurable f hf R) M (fun a b z => hb _ _) (fun b z => hb _ _)]
  simp only [remove_zero,remove_one,StabCross.training_cons]
include hf hb in
lemma training_identification (n : ℕ) :
    (∫ S, f (removeAt S 0) (S 0) * f (removeAt S 1) (S 1)
      ∂(Measure.pi fun _ : Fin (n+2) => D)) =
    ∫ R, LooCross.q D (trainingKernel f R) 0 1 0 0 1 1
      ∂(Measure.pi fun _ : Fin n => D) := by
  have hB (S : Fin (n+2) → Z) : |f (removeAt S 0) (S 0) * f (removeAt S 1) (S 1)| ≤ |M| * |M| := by
    rw [abs_mul]
    exact mul_le_mul (LooMoments.loss_bound f M hb S 0) (LooMoments.loss_bound f M hb S 1)
      (abs_nonneg _) (abs_nonneg _)
  rw [StabCross.integral_cons_two D (fun S : Fin (n+2) → Z => f (removeAt S 0) (S 0) * f (removeAt S 1) (S 1))
    ((LooMoments.loss_measurable f hf 0).mul (LooMoments.loss_measurable f hf 1)) (|M| * |M|) hB]
  apply integral_congr_ae
  filter_upwards [] with R
  unfold trainingKernel
  rw [LooCross.q_training D (fun a b z => f (a ::ₘ b ::ₘ trainingSet R) z) (fun b z => f (b ::ₘ trainingSet R) z) (two_measurable f hf R) (one_measurable f hf R) M (fun a b z => hb _ _) (fun b z => hb _ _)]
  simp only [remove_zero,remove_one,StabCross.training_cons,Fin.cons_zero,Fin.cons_one]
include hf hb in
lemma mixed_identification (n : ℕ) :
    (∫ S, (∫ z, f (trainingSet S) z ∂D) * f (removeAt S 0) (S 0)
      ∂(Measure.pi fun _ : Fin (n+2) => D)) =
    ∫ R, LooCross.q D (trainingKernel f R) 0 1 2 0 1 0
      ∂(Measure.pi fun _ : Fin n => D) := by
  have hB (S : Fin (n+2) → Z) : |(∫ z, f (trainingSet S) z ∂D) * f (removeAt S 0) (S 0)| ≤ |M| * |M| := by
    rw [abs_mul]
    exact mul_le_mul (StabMoments.risk_bound D f (hf _) M hb S) (LooMoments.loss_bound f M hb S 0)
      (abs_nonneg _) (abs_nonneg _)
  rw [StabCross.integral_cons_two D (fun S : Fin (n+2) → Z => (∫ z, f (trainingSet S) z ∂D) * f (removeAt S 0) (S 0))
    ((StabMoments.risk_measurable D f (hf _)).mul (LooMoments.loss_measurable f hf 0)) (|M| * |M|) hB]
  apply integral_congr_ae
  filter_upwards [] with R
  unfold trainingKernel
  rw [LooCross.q_mixed D (fun a b z => f (a ::ₘ b ::ₘ trainingSet R) z) (fun b z => f (b ::ₘ trainingSet R) z) (two_measurable f hf R) (one_measurable f hf R) M (fun a b z => hb _ _) (fun b z => hb _ _)]
  simp only [remove_zero,remove_one,StabCross.training_cons,Fin.cons_zero]
end LooFull

set_option backward.isDefEq.respectTransparency false
open MeasureTheory StabGen.Hypothesis
namespace LooFull
variable {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (f : Multiset Z → Z → ℝ)
    (hf : ∀ n, Measurable (fun p : (Fin n → Z) × Z => f (trainingSet p.1) p.2))
    (M : ℝ) (hb : ∀ T z, 0 ≤ f T z ∧ f T z ≤ M)
include hf in
lemma difference_measurable {m : ℕ} (i : Fin m) : Measurable (fun p : (Fin m → Z) × Z =>
    |f (trainingSet p.1) p.2 - f (removeAt p.1 i) p.2|) :=
  ((hf m).sub (LooMoments.removed_measurable f hf i)).abs
include hb in
lemma difference_bound {m : ℕ} (i : Fin m) (p : (Fin m → Z) × Z) :
    |f (trainingSet p.1) p.2 - f (removeAt p.1 i) p.2| ≤ |M| := by
  apply le_trans _ (le_abs_self M)
  apply abs_le.mpr
  constructor <;> linarith [(hb (trainingSet p.1) p.2).1,(hb (trainingSet p.1) p.2).2,
    (hb (removeAt p.1 i) p.2).1,(hb (removeAt p.1 i) p.2).2]
include hf hb in
lemma difference_prod {m : ℕ} (i : Fin m) :
    (∫ p : (Fin m → Z) × Z, |f (trainingSet p.1) p.2 - f (removeAt p.1 i) p.2|
      ∂((Measure.pi fun _ : Fin m => D).prod D)) =
    ∫ S, ∫ z, |f (trainingSet S) z - f (removeAt S i) z| ∂D
      ∂(Measure.pi fun _ : Fin m => D) := by
  apply integral_prod
  apply StabMoments.bounded_integrable _ (difference_measurable f hf i) |M|
  intro p
  simpa only [abs_abs] using difference_bound f M hb i p
include hf in
lemma difference_average_measurable {m : ℕ} (i : Fin m) :
    Measurable (fun S => ∫ z, |f (trainingSet S) z - f (removeAt S i) z| ∂D) :=
  (difference_measurable f hf i).stronglyMeasurable.integral_prod_right'.measurable
include hb in
lemma difference_average_bound {m : ℕ} (i : Fin m) (S : Fin m → Z) :
    |∫ z, |f (trainingSet S) z - f (removeAt S i) z| ∂D| ≤ |M| := by
  calc
    _ ≤ ∫ z, abs (|f (trainingSet S) z - f (removeAt S i) z|) ∂D := abs_integral_le_integral_abs
    _ ≤ ∫ _ : Z, |M| ∂D := integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
      (integrable_const _) (Filter.Eventually.of_forall fun z => by simpa only [abs_abs] using difference_bound f M hb i (S,z))
    _ = _ := by simp
include hf hb in
lemma difference_invariant {m : ℕ} (i k : Fin m) :
    (∫ p : (Fin m → Z) × Z, |f (trainingSet p.1) p.2 - f (removeAt p.1 i) p.2|
      ∂((Measure.pi fun _ : Fin m => D).prod D)) =
    ∫ p : (Fin m → Z) × Z, |f (trainingSet p.1) p.2 - f (removeAt p.1 k) p.2|
      ∂((Measure.pi fun _ : Fin m => D).prod D) := by
  rw [difference_prod D f hf M hb i,difference_prod D f hf M hb k]
  have h := StabMoments.integral_permutation D (Equiv.swap i k)
    (fun S => ∫ z, |f (trainingSet S) z - f (removeAt S i) z| ∂D)
  simpa only [LooMoments.remove_permutation,StabMoments.training_permutation,Function.comp_apply,Equiv.swap_apply_left] using h.symm
include hf hb in
lemma difference_identification (n : ℕ) :
    (∫ p : (Fin (n+2) → Z) × Z, |f (trainingSet p.1) p.2 - f (removeAt p.1 0) p.2|
      ∂((Measure.pi fun _ : Fin (n+2) => D).prod D)) =
    ∫ R, LooCross.d D (trainingKernel f R) 0 1 2 2 1 2
      ∂(Measure.pi fun _ : Fin n => D) := by
  rw [difference_prod D f hf M hb,
    StabCross.integral_cons_two D _ (difference_average_measurable D f hf 0) |M|
      (difference_average_bound D f M hb 0)]
  apply integral_congr_ae
  filter_upwards [] with R
  unfold trainingKernel
  rw [LooCross.d_deleted D (fun a b z => f (a ::ₘ b ::ₘ trainingSet R) z) (fun b z => f (b ::ₘ trainingSet R) z) (two_measurable f hf R) (one_measurable f hf R) M (fun a b z => hb _ _) (fun b z => hb _ _)]
  simp only [remove_zero,StabCross.training_cons,Fin.cons_zero]
end LooFull

set_option backward.isDefEq.respectTransparency false
open MeasureTheory StabGen.Hypothesis
namespace LooFull
variable {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (f : Multiset Z → Z → ℝ)
    (hf : ∀ n, Measurable (fun p : (Fin n → Z) × Z => f (trainingSet p.1) p.2))
    (M : ℝ) (hb : ∀ T z, 0 ≤ f T z ∧ f T z ≤ M)
include hf hb in
lemma sample_cross_bound (n : ℕ) :
    (∫ S, (∫ z, f (trainingSet S) z ∂D)^2 ∂(Measure.pi fun _ : Fin (n+2) => D)) +
    (∫ S, f (removeAt S 0) (S 0) * f (removeAt S 1) (S 1)
      ∂(Measure.pi fun _ : Fin (n+2) => D)) -
    2*(∫ S, (∫ z, f (trainingSet S) z ∂D) * f (removeAt S 0) (S 0)
      ∂(Measure.pi fun _ : Fin (n+2) => D)) ≤
    3*M*(∫ p : (Fin (n+2) → Z) × Z,
      |f (trainingSet p.1) p.2 - f (removeAt p.1 0) p.2|
      ∂((Measure.pi fun _ : Fin (n+2) => D).prod D)) := by
  rw [fresh_identification D f hf M hb n,training_identification D f hf M hb n,
    mixed_identification D f hf M hb n,difference_identification D f hf M hb n]
  exact random_training_cross f hf M hb D n
include hf hb in
lemma diagonal_gap {m : ℕ} (i j : Fin m) :
    M*(∫ S,f (removeAt S i) (S i) ∂(Measure.pi fun _ : Fin m => D)) -
    (∫ S,f (removeAt S i) (S i)*f (removeAt S j) (S j)
      ∂(Measure.pi fun _ : Fin m => D)) ≤ M^2/2 := by
  have h := StabDiagonal.equal_mean_pair (Measure.pi fun _ : Fin m => D)
    (fun S => f (removeAt S i) (S i)) (fun S => f (removeAt S j) (S j))
    (LooMoments.loss_measurable f hf i) (LooMoments.loss_measurable f hf j)
    M (fun S => hb _ _) (fun S => hb _ _) (LooMoments.diagonal_invariant f D i j id)
  have he : (fun S : Fin m → Z => f (removeAt S i) (S i) * (M-f (removeAt S j) (S j))) =
      (fun S => M*f (removeAt S i) (S i) - f (removeAt S i) (S i)*f (removeAt S j) (S j)) := by
    funext S; ring
  rw [he,integral_sub ((LooMoments.loss_integrable D f hf M hb i).const_mul M)
    (LooMoments.loss_product_integrable D f hf M hb i j),integral_const_mul] at h
  exact h
include hf hb in
theorem loo_bound_two (n : ℕ) (i : Fin (n+2)) :
    (∫ S, ((∫ z, f (trainingSet S) z ∂D) - LooMoments.emp f S)^2
      ∂(Measure.pi fun _ : Fin (n+2) => D)) ≤
      M^2/(2*((n+2:ℕ):ℝ)) + 3*M*(∫ p : (Fin (n+2) → Z) × Z,
        |f (trainingSet p.1) p.2 - f (removeAt p.1 i) p.2|
        ∂((Measure.pi fun _ : Fin (n+2) => D).prod D)) := by
  have hne : (0 : Fin (n+2)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  have hd := LooMoments.deviation_bound D f hf M hb (by omega : 0<n+2) 0 1 hne
  rw [StabMoments.fresh_square D f (hf (n+2)) M hb,
    LooMoments.fresh_mixed D f hf M hb,← LooMoments.heldout_expectation D f hf M hb (0 : Fin (n+2))] at hd
  have hc := sample_cross_bound D f hf M hb n
  rw [difference_invariant D f hf M hb 0 i] at hc
  have hg := diagonal_gap D f hf M hb (0 : Fin (n+2)) 1
  have hg' := mul_le_mul_of_nonneg_left hg (show 0 ≤ 1 / ((n+2 : ℕ) : ℝ) by positivity)
  have hscale : (1/((n+2:ℕ):ℝ))*(M^2/2) = M^2/(2*((n+2:ℕ):ℝ)) := by ring
  rw [hscale] at hg'
  have hform (a b : ℝ) : (1/((n+2:ℕ):ℝ))*(M*a-b) = M/((n+2:ℕ):ℝ)*a - 1/((n+2:ℕ):ℝ)*b := by ring
  rw [hform] at hg'
  linarith only [hd,hc,hg']
include hf hb in
theorem loo_bound (m : ℕ) (hm : 2 ≤ m) (i : Fin m) :
    (∫ S, ((∫ z, f (trainingSet S) z ∂D) - LooMoments.emp f S)^2
      ∂(Measure.pi fun _ : Fin m => D)) ≤
      M^2/(2*(m:ℝ)) + 3*M*(∫ p : (Fin m → Z) × Z,
        |f (trainingSet p.1) p.2 - f (removeAt p.1 i) p.2|
        ∂((Measure.pi fun _ : Fin m => D).prod D)) := by
  obtain ⟨n,rfl⟩ : ∃ n, m = n+2 := ⟨m-2,by omega⟩
  exact loo_bound_two D f hf M hb n i
end LooFull

open FoundationsML.Stability in
theorem loo_solution {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ) (M : ℝ)
    (hL : ∀ (y' : Y') (y : Y), 0 ≤ L y' y ∧ L y' y ≤ M)
    (A : LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable (fun p : (Fin n → X × Y) × (X × Y) =>
      Loss L (A (trainingSet p.1)) p.2))
    (m : ℕ) (hm : 2 ≤ m) (i : Fin m) :
    ∫ S : Fin m → X × Y,
        (GeneralizationError D L (A (trainingSet S)) - looError L A S) ^ 2
      ∂(Measure.pi fun _ : Fin m => D)
    ≤ M ^ 2 / (2 * (m : ℝ))
      + 3 * M * ∫ p : (Fin m → X × Y) × (X × Y),
          |Loss L (A (trainingSet p.1)) p.2
            - Loss L (A (removeAt p.1 i)) p.2|
        ∂((Measure.pi fun _ : Fin m => D).prod D) := by
  simpa only [GeneralizationError,looError,LooMoments.emp] using
    LooFull.loo_bound D (fun T z => Loss L (A T) z) hA M (fun T z => hL (A T z.1) z.2) m hm i
#print axioms loo_solution

open MeasureTheory StabGen.Hypothesis

open FoundationsML.Stability

theorem solution {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ) (M : ℝ)
    (hL : ∀ (y' : Y') (y : Y), 0 ≤ L y' y ∧ L y' y ≤ M)
    (A : LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable (fun p : (Fin n → X × Y) × (X × Y) =>
      Loss L (A (trainingSet p.1)) p.2))
    (m : ℕ) (hm : 2 ≤ m) (β₁ : ℝ) (h₁ : HypothesisStable D L A m β₁) :
    ∫ S : Fin m → X × Y,
        (GeneralizationError D L (A (trainingSet S)) - looError L A S) ^ 2
      ∂(Measure.pi fun _ : Fin m => D)
    ≤ M ^ 2 / (2 * (m : ℝ)) + 3 * M * β₁ := by
  let f : Multiset (X × Y) → (X × Y) → ℝ := fun T z => Loss L (A T) z
  have hb (T : Multiset (X × Y)) (z : X × Y) : 0 ≤ f T z ∧ f T z ≤ M := hL _ _
  have hM : 0 ≤ M := by
    have h := StabMoments.risk_bounds D f (hA 0) M hb (Fin.elim0 : Fin 0 → X × Y)
    exact h.1.trans h.2
  let i : Fin m := ⟨0,by omega⟩
  have hbase := LooFull.loo_bound D f hA M hb m hm i
  have h := hbase.trans (add_le_add (le_refl (M^2/(2*(m:ℝ))))
    (mul_le_mul_of_nonneg_left (h₁ i).2 (mul_nonneg (by norm_num : (0:ℝ)≤3) hM)))
  simpa only [f,GeneralizationError,looError,LooMoments.emp] using h


#print axioms solution

end LooPrior

open MeasureTheory
namespace StabSingleton
open LooPrior
lemma transfer {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x y : Ω → ℝ) (hx : Measurable x) (hy : Measurable y) (M B β : ℝ)
    (hM : 0 ≤ M) (bx : ∀ s, |x s| ≤ M) (by' : ∀ s, |y s| ≤ M)
    (hbase : (∫ s, y s^2 ∂μ) ≤ B) (hchange : (∫ s, |x s-y s| ∂μ) ≤ β) :
    (∫ s, x s^2 ∂μ) ≤ B+2*M*β := by
  have ix := StabMoments.bounded_integrable μ hx M bx
  have iy := StabMoments.bounded_integrable μ hy M by'
  have ix2 := StabMoments.bounded_product μ hx hx M bx bx
  have iy2 := StabMoments.bounded_product μ hy hy M by' by'
  simp only [← pow_two] at ix2 iy2
  have point (s : Ω) : x s^2 ≤ y s^2+2*M*|x s-y s| := by
    have ha := abs_le.mp (bx s);have hb := abs_le.mp (by' s)
    have hab1 := le_abs_self (x s-y s)
    have hab2 := neg_le_abs (x s-y s)
    have hmul := abs_mul (x s-y s) (x s+y s)
    have hsum : |x s+y s| ≤ 2*M := (abs_add_le _ _).trans (by linarith [bx s,by' s])
    have hh := mul_le_mul_of_nonneg_left hsum (abs_nonneg (x s-y s))
    rw [← hmul] at hh
    have he : x s^2-y s^2=(x s-y s)*(x s+y s) := by ring
    have hh' := (le_abs_self (x s^2-y s^2)).trans (by simpa only [he] using hh)
    nlinarith
  calc
    _ ≤ ∫ s, y s^2+2*M*|x s-y s| ∂μ :=
      integral_mono ix2 (iy2.add ((ix.sub iy).abs.const_mul (2*M))) point
    _ = (∫ s, y s^2 ∂μ)+2*M*(∫ s, |x s-y s| ∂μ) := by
      have ha := integral_add iy2 ((ix.sub iy).abs.const_mul (2*M))
      simp only [Pi.sub_apply,Pi.mul_apply,Pi.add_apply] at ha
      rw [ha,integral_const_mul]
    _ ≤ B+2*M*β := add_le_add hbase (mul_le_mul_of_nonneg_left hchange (by positivity))

open StabGen.Hypothesis
lemma moments {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (f : Multiset Z → Z → ℝ)
    (hf : ∀ n, Measurable (fun p : (Fin n → Z) × Z => f (trainingSet p.1) p.2))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ T z, 0 ≤ f T z ∧ f T z ≤ M)
    (β₁ β₂ : ℝ) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (h₁ : (∫ p : (Fin 1 → Z) × Z, |f (trainingSet p.1) p.2-f 0 p.2|
      ∂((Measure.pi fun _ : Fin 1 => D).prod D)) ≤ β₁)
    (h₂ : (∫ S : Fin 1 → Z, |f (trainingSet S) (S 0)-f 0 (S 0)|
      ∂(Measure.pi fun _ : Fin 1 => D)) ≤ β₂) :
    (∫ S : Fin 1 → Z, ((∫ z, f (trainingSet S) z ∂D)-f (trainingSet S) (S 0))^2
      ∂(Measure.pi fun _ : Fin 1 => D)) ≤ M^2/2+3*M*(β₁+β₂) ∧
    (∫ S : Fin 1 → Z, ((∫ z, f (trainingSet S) z ∂D)-f 0 (S 0))^2
      ∂(Measure.pi fun _ : Fin 1 => D)) ≤ M^2/2+3*M*β₁ := by
  let μ := Measure.pi fun _ : Fin 1 => D
  let g : Z → ℝ := f 0
  let r : (Fin 1 → Z) → ℝ := fun S => ∫ z, f (trainingSet S) z ∂D
  let r₀ : ℝ := ∫ z, g z ∂D
  let v : (Fin 1 → Z) → ℝ := fun S => g (S 0)
  let u : (Fin 1 → Z) → ℝ := fun S => f (trainingSet S) (S 0)
  have bg (z : Z) : 0 ≤ g z ∧ g z ≤ M := hb 0 z
  have ab (T : Multiset Z) (z : Z) : |f T z| ≤ M := by rw [abs_of_nonneg (hb T z).1];exact (hb T z).2
  have hg : Measurable g := by
    simpa [g,trainingSet,Function.comp_def] using (hf 0).comp
      ((show Measurable (fun _ : Z => (Fin.elim0 : Fin 0 → Z)) from measurable_const).prodMk measurable_id)
  have ig := StabMoments.bounded_integrable D hg M (ab 0)
  have br₀ : 0 ≤ r₀ ∧ r₀ ≤ M := by
    refine ⟨integral_nonneg (fun z => (bg z).1),?_⟩
    exact (integral_mono ig (integrable_const M) (fun z => (bg z).2)).trans_eq (by simp)
  have hr : Measurable r := StabMoments.risk_measurable D f (hf 1)
  have br (S : Fin 1 → Z) : 0 ≤ r S ∧ r S ≤ M := StabMoments.risk_bounds D f (hf 1) M hb S
  have hv : Measurable v := hg.comp (measurable_pi_apply 0)
  have hu : Measurable u := StabMoments.loss_measurable f (hf 1) 0
  have bv (S : Fin 1 → Z) : 0 ≤ v S ∧ v S ≤ M := bg (S 0)
  have bu (S : Fin 1 → Z) : 0 ≤ u S ∧ u S ≤ M := hb _ _
  have ir := StabMoments.bounded_integrable μ hr M (fun S => by rw [abs_of_nonneg (br S).1];exact (br S).2)
  have iu := StabMoments.bounded_integrable μ hu M (fun S => ab _ _)
  have iv := StabMoments.bounded_integrable μ hv M (fun S => ab _ _)
  have idiff : Integrable (fun p : (Fin 1 → Z) × Z => |f (trainingSet p.1) p.2-g p.2|) (μ.prod D) := by
    apply StabMoments.bounded_integrable _ (((hf 1).sub (hg.comp measurable_snd)).abs) (2*M)
    intro p
    rw [abs_abs]
    apply (abs_sub _ _).trans
    change |f (trainingSet p.1) p.2|+|f 0 p.2| ≤ 2*M
    linarith [ab (trainingSet p.1) p.2,ab 0 p.2]
  have hrchange : (∫ S, |r S-r₀| ∂μ) ≤ β₁ := by
    calc
      _ ≤ ∫ S, (∫ z, |f (trainingSet S) z-g z| ∂D) ∂μ := by
        apply integral_mono (ir.sub (integrable_const _)).abs idiff.integral_prod_left
        intro S
        change |(∫ z, f (trainingSet S) z ∂D)-(∫ z, g z ∂D)| ≤ _
        rw [← integral_sub (StabMoments.fresh_integrable D f (hf 1) M hb S) ig]
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (fun z => f (trainingSet S) z-g z))
      _ = ∫ p : (Fin 1 → Z) × Z, |f (trainingSet p.1) p.2-g p.2| ∂(μ.prod D) :=
        (integral_prod _ idiff).symm
      _ ≤ β₁ := h₁
  have hvmean : (∫ S, v S ∂μ) = r₀ := by
    change (∫ S, g (S 0) ∂μ) = ∫ z, g z ∂D
    have hmap := (measurePreserving_eval (fun _ : Fin 1 => D) 0).map_eq
    calc
      _ = ∫ z, g z ∂(μ.map (fun S => S 0)) :=
        (integral_map (measurable_pi_apply 0).aemeasurable hg.aestronglyMeasurable).symm
      _ = _ := by rw [hmap]
  have hvar := ProbabilityTheory.variance_le_sq_of_bounded
    (μ := μ) (X := v) (Filter.Eventually.of_forall bv) hv.aemeasurable
  rw [ProbabilityTheory.variance_eq_integral hv.aemeasurable,hvmean] at hvar
  have hbase : (∫ S, (r₀-v S)^2 ∂μ) ≤ M^2/2 := by
    have he : (fun S => (r₀-v S)^2) = (fun S => (v S-r₀)^2) := by funext S;ring
    rw [he]
    nlinarith [sq_nonneg M]
  have bdiff (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ M) (hb' : 0 ≤ b ∧ b ≤ M) : |a-b| ≤ M :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  have hemp : (∫ S, |(r S-u S)-(r₀-v S)| ∂μ) ≤ β₁+β₂ := by
    calc
      _ ≤ ∫ S, (|r S-r₀|+|u S-v S|) ∂μ := by
        apply integral_mono ((ir.sub iu).sub ((integrable_const _).sub iv)).abs
          (((ir.sub (integrable_const _)).abs).add (iu.sub iv).abs)
        intro S
        change |(r S-u S)-(r₀-v S)| ≤ |r S-r₀|+|u S-v S|
        have he : (r S-u S)-(r₀-v S)=(r S-r₀)-(u S-v S) := by ring
        rw [he]
        exact abs_sub _ _
      _ = (∫ S, |r S-r₀| ∂μ)+(∫ S, |u S-v S| ∂μ) :=
        integral_add (ir.sub (integrable_const _)).abs (iu.sub iv).abs
      _ ≤ β₁+β₂ := add_le_add hrchange h₂
  have he := transfer μ (fun S => r S-u S) (fun S => r₀-v S)
    (hr.sub hu) (measurable_const.sub hv) M (M^2/2) (β₁+β₂) hM
    (fun S => bdiff _ _ (br S) (bu S)) (fun S => bdiff _ _ br₀ (bv S)) hbase hemp
  have hlo : (∫ S, |(r S-v S)-(r₀-v S)| ∂μ) ≤ β₁ := by simpa using hrchange
  have hl := transfer μ (fun S => r S-v S) (fun S => r₀-v S)
    (hr.sub hv) (measurable_const.sub hv) M (M^2/2) β₁ hM
    (fun S => bdiff _ _ (br S) (bv S)) (fun S => bdiff _ _ br₀ (bv S)) hbase hlo
  constructor
  · change (∫ S, (r S-u S)^2 ∂μ) ≤ _
    nlinarith [mul_nonneg hM hβ₁,mul_nonneg hM hβ₂]
  · change (∫ S, (r S-v S)^2 ∂μ) ≤ _
    nlinarith [mul_nonneg hM hβ₁]
end StabSingleton

open MeasureTheory
namespace StabTail
lemma square_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (g : Ω → ℝ) (hi : Integrable (fun x => g x ^ 2) μ)
    (B : ℝ) (hb : (∫ x, g x^2 ∂μ) ≤ B)
    (δ : ℝ) (hδ : 0 < δ) :
    μ {x | Real.sqrt (B/δ) < g x} ≤ ENNReal.ofReal δ := by
  have hB : 0 ≤ B := (integral_nonneg (fun x => sq_nonneg (g x))).trans hb
  by_cases hzero : B = 0
  · have hint : (∫ x, g x^2 ∂μ) = 0 := le_antisymm (by simpa [hzero] using hb)
      (integral_nonneg (fun x => sq_nonneg (g x)))
    have hz := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (g x)) hi).mp hint
    have he : ∀ᵐ x ∂μ, x ∉ {x | Real.sqrt (B/δ) < g x} := by
      filter_upwards [hz] with x hx
      simp only [Pi.zero_apply] at hx
      simp only [Set.mem_setOf_eq,hzero,zero_div,Real.sqrt_zero,not_lt]
      nlinarith [sq_nonneg (g x)]
    have hn : μ {x | Real.sqrt (B/δ) < g x} = 0 := by
      simpa only [ae_iff,Set.compl_setOf,not_not,Set.mem_setOf_eq] using he
    rw [hn]
    exact bot_le
  · have ht : 0 < B/δ := div_pos (lt_of_le_of_ne hB (Ne.symm hzero)) hδ
    have hsub : μ {x | Real.sqrt (B/δ) < g x} ≤
        ENNReal.ofReal (∫ x, g x^2/(B/δ) ∂μ) := by
      apply (hi.div_const (B/δ)).measure_le_integral
      · exact Filter.Eventually.of_forall (fun x => div_nonneg (sq_nonneg _) ht.le)
      · intro x hx
        apply (le_div_iff₀ ht).mpr
        have hs := Real.sq_sqrt ht.le
        have hsn := Real.sqrt_nonneg (B/δ)
        change Real.sqrt (B/δ) < g x at hx
        nlinarith
    apply hsub.trans
    apply ENNReal.ofReal_le_ofReal
    rw [integral_div]
    apply (div_le_iff₀ ht).mpr
    have hden : δ*(B/δ) = B := by field_simp
    rwa [hden]
end StabTail

open MeasureTheory StabGen.Hypothesis FoundationsML.Stability

theorem solution {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ) (M : ℝ)
    (hL : ∀ (y' : Y') (y : Y), 0 ≤ L y' y ∧ L y' y ≤ M)
    (A : LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable (fun p : (Fin n → X × Y) × (X × Y) =>
      Loss L (A (trainingSet p.1)) p.2))
    (m : ℕ) (hm : 1 ≤ m) (β₁ β₂ : ℝ) (h₁ : HypothesisStable D L A m β₁)
    (h₂ : PointwiseHypothesisStable D L A m β₂) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin m => D)
        {S | EmpiricalError L S (A (trainingSet S))
              + Real.sqrt ((M ^ 2 + 6 * M * (m : ℝ) * (β₁ + β₂)) / (2 * (m : ℝ) * δ))
            < GeneralizationError D L (A (trainingSet S))} ≤ ENNReal.ofReal δ ∧
    (Measure.pi fun _ : Fin m => D)
        {S | looError L A S
              + Real.sqrt ((M ^ 2 + 6 * M * (m : ℝ) * β₁) / (2 * (m : ℝ) * δ))
            < GeneralizationError D L (A (trainingSet S))} ≤ ENNReal.ofReal δ := by
  let f : Multiset (X × Y) → (X × Y) → ℝ := fun T z => Loss L (A T) z
  have hb (T : Multiset (X × Y)) (z : X × Y) : 0 ≤ f T z ∧ f T z ≤ M := hL _ _
  have hM : 0 ≤ M := by
    have h := LooPrior.StabMoments.risk_bounds D f (hA 0) M hb (Fin.elim0 : Fin 0 → X × Y)
    exact h.1.trans h.2
  let i : Fin m := ⟨0,by omega⟩
  have hb₁ : 0 ≤ β₁ := (integral_nonneg (fun p : (Fin m → X × Y) × (X × Y) =>
    abs_nonneg (Loss L (A (trainingSet p.1)) p.2-Loss L (A (removeAt p.1 i)) p.2))).trans (h₁ i).2
  have hb₂ : 0 ≤ β₂ := (integral_nonneg (fun S : Fin m → X × Y =>
    abs_nonneg (Loss L (A (trainingSet S)) (S i)-Loss L (A (removeAt S i)) (S i)))).trans (h₂ i).2
  have moments :
      (∫ S : Fin m → X × Y, (GeneralizationError D L (A (trainingSet S))-
        EmpiricalError L S (A (trainingSet S)))^2 ∂(Measure.pi fun _ : Fin m => D))
        ≤ M^2/(2*(m:ℝ))+3*M*(β₁+β₂) ∧
      (∫ S : Fin m → X × Y, (GeneralizationError D L (A (trainingSet S))-
        looError L A S)^2 ∂(Measure.pi fun _ : Fin m => D)) ≤ M^2/(2*(m:ℝ))+3*M*β₁ := by
    by_cases hm2 : 2 ≤ m
    · exact ⟨EmpiricalPrior.solution D L M hL A hA m hm2 β₁ β₂ h₁ h₂,
        LooPrior.solution D L M hL A hA m hm2 β₁ h₁⟩
    · have hm1 : m = 1 := by omega
      subst m
      have hrem (S : Fin 1 → X × Y) (j : Fin 1) : removeAt S j = 0 := by
        fin_cases j
        have hfin : (Finset.univ : Finset (Fin 1)).erase 0 = ∅ := by decide
        simp [removeAt,hfin]
      have hs := StabSingleton.moments D f hA M hM hb β₁ β₂ hb₁ hb₂
        (by simpa only [f,hrem] using (h₁ 0).2)
        (by simpa only [f,hrem] using (h₂ 0).2)
      simpa [f,GeneralizationError,EmpiricalError,looError,hrem] using hs
  let μ := Measure.pi fun _ : Fin m => D
  let r : (Fin m → X × Y) → ℝ := fun S => GeneralizationError D L (A (trainingSet S))
  let e : (Fin m → X × Y) → ℝ := fun S => EmpiricalError L S (A (trainingSet S))
  let l : (Fin m → X × Y) → ℝ := fun S => looError L A S
  have hr : Measurable r := LooPrior.StabMoments.risk_measurable D f (hA m)
  have he : Measurable e := EmpiricalPrior.StabMoments.emp_measurable f (hA m) M hb
  have hl : Measurable l := LooPrior.LooMoments.emp_measurable f hA M hb
  have br (S : Fin m → X × Y) : |r S| ≤ |M| := LooPrior.StabMoments.risk_bound D f (hA m) M hb S
  have be (S : Fin m → X × Y) : |e S| ≤ |M| := EmpiricalPrior.StabMoments.emp_bound f (hA m) M hb (by omega) S
  have bl (S : Fin m → X × Y) : |l S| ≤ |M| := LooPrior.LooMoments.emp_bound f hA M hb (by omega) S
  have integrableGap (a : (Fin m → X × Y) → ℝ) (ha : Measurable a)
      (ba : ∀ S, |a S| ≤ |M|) : Integrable (fun S => (r S-a S)^2) μ := by
    have b (S : Fin m → X × Y) : |r S-a S| ≤ 2*|M| :=
      (abs_sub _ _).trans (by linarith [br S,ba S])
    simpa only [pow_two,Pi.sub_apply] using LooPrior.StabMoments.bounded_product μ (hr.sub ha) (hr.sub ha)
      (2*|M|) b b
  have hEm := StabTail.square_tail μ (fun S => r S-e S) (integrableGap e he be)
    (M^2/(2*(m:ℝ))+3*M*(β₁+β₂)) moments.1 δ hδ
  have hLo := StabTail.square_tail μ (fun S => r S-l S) (integrableGap l hl bl)
    (M^2/(2*(m:ℝ))+3*M*β₁) moments.2 δ hδ
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have algebra (b : ℝ) : (M^2/(2*(m:ℝ))+3*M*b)/δ =
      (M^2+6*M*(m:ℝ)*b)/(2*(m:ℝ)*δ) := by field_simp;ring
  rw [algebra] at hEm hLo
  simpa only [μ,r,e,l,lt_sub_iff_add_lt,add_comm] using And.intro hEm hLo
