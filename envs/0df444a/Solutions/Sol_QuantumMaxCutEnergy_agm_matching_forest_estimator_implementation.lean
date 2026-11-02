-- Prove2me | solution 1 for QuantumMaxCutEnergy.agm_matching_forest_estimator_implementation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T14:52:16.763484+00:00
-- url     : https://prove2.me/submissions/041f2108-bf11-4c31-a2da-d3ea16f70a03

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

/-! Complete matching/forest numerical estimator implementation.
Published research source: Anshu, Gosset, Morenz, TQC 2020,
https://doi.org/10.4230/LIPIcs.TQC.2020.7, Lemma 5, Lemma 7, Eqs. (25)--(26).
The imported shared definition supplies only the already compiled finite
classical arithmetic/parser and the concrete incident-floor program. -/


-- Proof source: baseline/next-half/Antisymmetrizer.lean


noncomputable section
namespace QuantumMaxCutEnergy.Star

def swapWave {n : ℕ} (a b : Fin n) (ψ : Wave n) : Wave n :=
  fun x => ψ (x ∘ Equiv.swap a b)

def edgeAction {n : ℕ} (a b : Fin n) (ψ : Wave n) : Wave n :=
  ψ - swapWave a b ψ

lemma same_swap {α β : Type*} [DecidableEq α] (x : α → β) (a b : α)
    (h : x a = x b) : x ∘ Equiv.swap a b = x := by
  funext k
  by_cases hka : k = a <;> by_cases hkb : k = b <;>
    simp_all [Function.comp_apply, Equiv.swap_apply_def]

lemma cross_same_center {α β : Type*} [DecidableEq α] (x : α → β)
    (c i j : α) (hci : c ≠ i) (hcj : c ≠ j) (hij : i ≠ j)
    (h : x c = x i) :
    (x ∘ Equiv.swap c j) ∘ Equiv.swap c i = x ∘ Equiv.swap i j := by
  have hic : i ≠ c := hci.symm
  have hjc : j ≠ c := hcj.symm
  have hji : j ≠ i := hij.symm
  funext k
  by_cases hkc : k = c <;> by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp_all [Function.comp_apply, Equiv.swap_apply_def]

lemma cross_same_leaves {α β : Type*} [DecidableEq α] (x : α → β)
    (c i j : α) (hci : c ≠ i) (hcj : c ≠ j) (hij : i ≠ j)
    (h : x i = x j) :
    (x ∘ Equiv.swap c i) ∘ Equiv.swap c j = x ∘ Equiv.swap c i := by
  have hic : i ≠ c := hci.symm
  have hjc : j ≠ c := hcj.symm
  have hji : j ≠ i := hij.symm
  funext k
  by_cases hkc : k = c <;> by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp_all [Function.comp_apply, Equiv.swap_apply_def]

lemma bool_three_equal (a b c : Bool) : a = b ∨ a = c ∨ b = c := by
  cases a <;> cases b <;> cases c <;> simp

/-- The three-qubit antisymmetrizer vanishes because a Boolean basis string
has equal bits at two of the three positions. -/
lemma antisymmetrizer_pointwise {n : ℕ} (ψ : Wave n) (x : Basis n)
    (c i j : Fin n) (hci : c ≠ i) (hcj : c ≠ j) (hij : i ≠ j) :
    ψ x - swapWave c i ψ x - swapWave c j ψ x - swapWave i j ψ x +
      swapWave c i (swapWave c j ψ) x +
      swapWave c j (swapWave c i ψ) x = 0 := by
  rcases bool_three_equal (x c) (x i) (x j) with h | h | h
  · have hs := same_swap x c i h
    have ht := cross_same_center x c i j hci hcj hij h
    simp only [swapWave, hs, ht]
    ring
  · have hs := same_swap x c j h
    have ht := cross_same_center x c j i hcj hci hij.symm h
    have ht' : (x ∘ Equiv.swap c i) ∘ Equiv.swap c j = x ∘ Equiv.swap i j := by
      simpa only [Equiv.swap_comm j i] using ht
    simp only [swapWave, hs, ht']
    ring
  · have hs := same_swap x i j h
    have ht := cross_same_leaves x c i j hci hcj hij h
    have hu := cross_same_leaves x c j i hcj hci hij.symm h.symm
    simp only [swapWave, hs, ht, hu]
    ring

theorem antisymmetrizer {n : ℕ} (ψ : Wave n)
    (c i j : Fin n) (hci : c ≠ i) (hcj : c ≠ j) (hij : i ≠ j) :
    ψ - swapWave c i ψ - swapWave c j ψ - swapWave i j ψ +
      swapWave c i (swapWave c j ψ) +
      swapWave c j (swapWave c i ψ) = 0 := by
  funext x
  exact antisymmetrizer_pointwise ψ x c i j hci hcj hij

/-- In the QMC convention h=I-SWAP, products of two edges with a shared
center reduce to three edge operators. -/
theorem shared_center_anticommutator {n : ℕ} (ψ : Wave n)
    (c i j : Fin n) (hci : c ≠ i) (hcj : c ≠ j) (hij : i ≠ j) :
    edgeAction c i (edgeAction c j ψ) + edgeAction c j (edgeAction c i ψ) =
      edgeAction c i ψ + edgeAction c j ψ - edgeAction i j ψ := by
  funext x
  have h := antisymmetrizer_pointwise ψ x c i j hci hcj hij
  simp only [edgeAction, swapWave, Pi.add_apply, Pi.sub_apply] at h ⊢
  linear_combination h

end QuantumMaxCutEnergy.Star



-- Proof source: baseline/next-half/RealInner.lean


noncomputable section
namespace QuantumMaxCutEnergy.Star

def swapBasis {n : ℕ} (a b : Fin n) : Basis n ≃ Basis n where
  toFun x := x ∘ Equiv.swap a b
  invFun x := x ∘ Equiv.swap a b
  left_inv x := by funext i; simp [Function.comp_def]
  right_inv x := by funext i; simp [Function.comp_def]

/-- The real part of the usual inner product, written as a finite real sum. -/
def realInner {n : ℕ} (ψ φ : Wave n) : ℝ :=
  ∑ x, ((ψ x).re * (φ x).re + (ψ x).im * (φ x).im)

def realScale {n : ℕ} (a : ℝ) (ψ : Wave n) : Wave n :=
  fun x => (a : ℂ) * ψ x

lemma realInner_comm {n : ℕ} (ψ φ : Wave n) :
    realInner ψ φ = realInner φ ψ := by
  unfold realInner
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma realInner_self {n : ℕ} (ψ : Wave n) :
    realInner ψ ψ = squaredNorm ψ := by
  unfold realInner squaredNorm
  apply Finset.sum_congr rfl
  intro x _
  simp [Complex.normSq_apply]

lemma realInner_nonneg {n : ℕ} (ψ : Wave n) : 0 ≤ realInner ψ ψ := by
  rw [realInner_self]
  exact Finset.sum_nonneg fun x _ => Complex.normSq_nonneg _

@[simp] lemma realInner_zero_right {n : ℕ} (ψ : Wave n) : realInner ψ 0 = 0 := by
  simp [realInner]

lemma realInner_add_right {n : ℕ} (ψ φ χ : Wave n) :
    realInner ψ (φ + χ) = realInner ψ φ + realInner ψ χ := by
  unfold realInner
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Pi.add_apply, Complex.add_re, Complex.add_im]
  ring

lemma realInner_sub_right {n : ℕ} (ψ φ χ : Wave n) :
    realInner ψ (φ - χ) = realInner ψ φ - realInner ψ χ := by
  unfold realInner
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Pi.sub_apply, Complex.sub_re, Complex.sub_im]
  ring

lemma realInner_add_left {n : ℕ} (ψ φ χ : Wave n) :
    realInner (ψ + φ) χ = realInner ψ χ + realInner φ χ := by
  rw [realInner_comm, realInner_add_right]
  congr 1 <;> exact realInner_comm _ _

lemma realInner_sub_left {n : ℕ} (ψ φ χ : Wave n) :
    realInner (ψ - φ) χ = realInner ψ χ - realInner φ χ := by
  rw [realInner_comm, realInner_sub_right]
  congr 1 <;> exact realInner_comm _ _

lemma realInner_scale_right {n : ℕ} (a : ℝ) (ψ φ : Wave n) :
    realInner ψ (realScale a φ) = a * realInner ψ φ := by
  unfold realInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [realScale, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

lemma realInner_scale_left {n : ℕ} (a : ℝ) (ψ φ : Wave n) :
    realInner (realScale a ψ) φ = a * realInner ψ φ := by
  rw [realInner_comm, realInner_scale_right, realInner_comm φ ψ]

lemma realInner_sum_right {n : ℕ} {ι : Type*} (s : Finset ι)
    (ψ : Wave n) (φ : ι → Wave n) :
    realInner ψ (∑ i ∈ s, φ i) = ∑ i ∈ s, realInner ψ (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, realInner_add_right, ih]

lemma realInner_sum_left {n : ℕ} {ι : Type*} (s : Finset ι)
    (ψ : ι → Wave n) (φ : Wave n) :
    realInner (∑ i ∈ s, ψ i) φ = ∑ i ∈ s, realInner (ψ i) φ := by
  rw [realInner_comm, realInner_sum_right]
  apply Finset.sum_congr rfl
  intro i _
  exact realInner_comm _ _

lemma swapWave_twice {n : ℕ} (a b : Fin n) (ψ : Wave n) :
    swapWave a b (swapWave a b ψ) = ψ := by
  funext x
  simp [swapWave, Function.comp_def]

lemma swapWave_adjoint {n : ℕ} (a b : Fin n) (ψ φ : Wave n) :
    realInner (swapWave a b ψ) φ = realInner ψ (swapWave a b φ) := by
  unfold realInner
  have h := (swapBasis a b).sum_comp
    (fun x => (ψ x).re * (swapWave a b φ x).re +
      (ψ x).im * (swapWave a b φ x).im)
  simpa [swapBasis, swapWave, Function.comp_def] using h

lemma edgeAction_adjoint {n : ℕ} (a b : Fin n) (ψ φ : Wave n) :
    realInner (edgeAction a b ψ) φ = realInner ψ (edgeAction a b φ) := by
  simp only [edgeAction, realInner_sub_left, realInner_sub_right, swapWave_adjoint]

lemma edgeAction_twice {n : ℕ} (a b : Fin n) (ψ : Wave n) :
    edgeAction a b (edgeAction a b ψ) = realScale 2 (edgeAction a b ψ) := by
  funext x
  simp only [edgeAction, swapWave, Pi.sub_apply, realScale]
  have hs : (x ∘ Equiv.swap a b) ∘ Equiv.swap a b = x := by
    funext i
    simp [Function.comp_def]
  rw [hs]
  push_cast
  ring

def pairEnergy {n : ℕ} (a b : Fin n) (ψ : Wave n) : ℝ :=
  realInner ψ (edgeAction a b ψ)

lemma edgeAction_squaredNorm {n : ℕ} (a b : Fin n) (ψ : Wave n) :
    squaredNorm (edgeAction a b ψ) = 2 * pairEnergy a b ψ := by
  rw [← realInner_self, edgeAction_adjoint, edgeAction_twice,
    realInner_scale_right, pairEnergy]

lemma pairEnergy_nonneg {n : ℕ} (a b : Fin n) (ψ : Wave n) :
    0 ≤ pairEnergy a b ψ := by
  have h := realInner_nonneg (edgeAction a b ψ)
  rw [realInner_self, edgeAction_squaredNorm] at h
  linarith

lemma pairEnergy_eq {n : ℕ} (a b : Fin n) (ψ : Wave n) :
    pairEnergy a b ψ = (∑ x, Complex.normSq
      (ψ x - ψ (x ∘ Equiv.swap a b))) / 2 := by
  have h := edgeAction_squaredNorm a b ψ
  unfold squaredNorm edgeAction swapWave at h
  simp only [Pi.sub_apply] at h
  linarith

lemma shared_center_inner {n : ℕ} (ψ : Wave n) (c i j : Fin n)
    (hci : c ≠ i) (hcj : c ≠ j) (hij : i ≠ j) :
    2 * realInner (edgeAction c i ψ) (edgeAction c j ψ) =
      pairEnergy c i ψ + pairEnergy c j ψ - pairEnergy i j ψ := by
  have h := congrArg (realInner ψ)
    (shared_center_anticommutator ψ c i j hci hcj hij)
  simp only [realInner_add_right, realInner_sub_right] at h
  rw [← edgeAction_adjoint c i ψ (edgeAction c j ψ),
    ← edgeAction_adjoint c j ψ (edgeAction c i ψ)] at h
  have hc := realInner_comm (edgeAction c j ψ) (edgeAction c i ψ)
  unfold pairEnergy
  linarith

end QuantumMaxCutEnergy.Star



-- Proof source: baseline/next-half/WeightedStar.lean


noncomputable section
namespace QuantumMaxCutEnergy.Star

lemma edge_inner_le {n : ℕ} (ψ : Wave n) (c i j : Fin n)
    (hci : c ≠ i) (hcj : c ≠ j) :
    realInner (edgeAction c i ψ) (edgeAction c j ψ) ≤
      (pairEnergy c i ψ + pairEnergy c j ψ) / 2 +
        if i = j then pairEnergy c i ψ else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [realInner_self, edgeAction_squaredNorm]
    simp only [ite_true]
    linarith
  · have h := shared_center_inner ψ c i j hci hcj hij
    have hp := pairEnergy_nonneg i j ψ
    rw [if_neg hij]
    linarith

/-- A finite algebra identity used to sum the two-edge estimate. -/
lemma weighted_pair_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (w e : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j *
      ((e i + e j) / 2 + if i = j then e i else 0)) =
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * e i) +
        ∑ i ∈ s, w i * w i * e i := by
  have hrow (i : ι) (hi : i ∈ s) :
      (∑ j ∈ s, w i * w j *
        ((e i + e j) / 2 + if i = j then e i else 0)) =
        (w i * e i * (∑ j ∈ s, w j) +
          w i * (∑ j ∈ s, w j * e j)) / 2 + w i * w i * e i := by
    calc
      _ = (∑ j ∈ s, (w i * e i * w j + w i * (w j * e j)) / 2) +
          ∑ j ∈ s, if i = j then w i * w i * e i else 0 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        split_ifs with h
        · subst j
          ring
        · ring
      _ = _ := by
        rw [← Finset.sum_div, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
        simp [hi]
  calc
    _ = ∑ i ∈ s, ((w i * e i * (∑ j ∈ s, w j) +
        w i * (∑ j ∈ s, w j * e j)) / 2 + w i * w i * e i) := by
      apply Finset.sum_congr rfl
      exact hrow
    _ = _ := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul]
      ring

def starAction {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (w : Fin n → ℝ) (ψ : Wave n) : Wave n :=
  ∑ i ∈ s, realScale (w i) (edgeAction c i ψ)

def starEnergy {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (w : Fin n → ℝ) (ψ : Wave n) : ℝ :=
  ∑ i ∈ s, w i * pairEnergy c i ψ

lemma starEnergy_nonneg {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (w : Fin n → ℝ) (ψ : Wave n) (hw : ∀ i ∈ s, 0 ≤ w i) :
    0 ≤ starEnergy c s w ψ := by
  exact Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (pairEnergy_nonneg c i ψ)

lemma starAction_inner {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (w : Fin n → ℝ) (ψ : Wave n) :
    realInner ψ (starAction c s w ψ) = starEnergy c s w ψ := by
  unfold starAction starEnergy
  rw [realInner_sum_right]
  simp only [realInner_scale_right, pairEnergy]

lemma starAction_squaredNorm {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (w : Fin n → ℝ) (ψ : Wave n) :
    squaredNorm (starAction c s w ψ) =
      ∑ i ∈ s, ∑ j ∈ s, w i * w j *
        realInner (edgeAction c i ψ) (edgeAction c j ψ) := by
  rw [← realInner_self]
  unfold starAction
  rw [realInner_sum_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [realInner_sum_right]
  apply Finset.sum_congr rfl
  intro j hj
  rw [realInner_scale_left, realInner_scale_right]
  ring

lemma starAction_norm_bound {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (w : Fin n → ℝ) (ψ : Wave n) (M : ℝ)
    (hc : c ∉ s) (hw : ∀ i ∈ s, 0 ≤ w i) (hM : ∀ i ∈ s, w i ≤ M) :
    squaredNorm (starAction c s w ψ) ≤
      ((∑ i ∈ s, w i) + M) * starEnergy c s w ψ := by
  classical
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, w i * w j *
        ((pairEnergy c i ψ + pairEnergy c j ψ) / 2 +
          if i = j then pairEnergy c i ψ else 0) := by
      rw [starAction_squaredNorm]
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hw i hi) (hw j hj))
      apply edge_inner_le ψ c i j
      · exact fun h => hc (h ▸ hi)
      · exact fun h => hc (h ▸ hj)
    _ = (∑ i ∈ s, w i) * starEnergy c s w ψ +
        ∑ i ∈ s, w i * w i * pairEnergy c i ψ :=
      weighted_pair_sum s w (fun i => pairEnergy c i ψ)
    _ ≤ (∑ i ∈ s, w i) * starEnergy c s w ψ + M * starEnergy c s w ψ := by
      apply add_le_add_right
      unfold starEnergy
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      nlinarith [mul_nonneg (hw i hi) (pairEnergy_nonneg c i ψ),
        mul_le_mul_of_nonneg_right (hM i hi)
          (mul_nonneg (hw i hi) (pairEnergy_nonneg c i ψ))]
    _ = _ := by ring

lemma inner_sq_le_squaredNorm {n : ℕ} (ψ φ : Wave n) (hψ : squaredNorm ψ = 1) :
    realInner ψ φ ^ 2 ≤ squaredNorm φ := by
  have h := realInner_nonneg (φ - realScale (realInner ψ φ) ψ)
  simp only [realInner_sub_left, realInner_sub_right,
    realInner_scale_left, realInner_scale_right] at h
  rw [realInner_comm φ ψ, realInner_self ψ, hψ, realInner_self φ] at h
  nlinarith

/-- A nonnegative weighted QMC star has largest energy at most the total
incident weight plus an upper bound for its largest edge weight. -/
theorem weighted_star_upper_bound {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (w : Fin n → ℝ) (ψ : Wave n) (M : ℝ)
    (hc : c ∉ s) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hM0 : 0 ≤ M) (hM : ∀ i ∈ s, w i ≤ M) (hψ : squaredNorm ψ = 1) :
    starEnergy c s w ψ ≤ (∑ i ∈ s, w i) + M := by
  have hnorm := starAction_norm_bound c s w ψ M hc hw hM
  have hcs := inner_sq_le_squaredNorm ψ (starAction c s w ψ) hψ
  rw [starAction_inner] at hcs
  have hpos := starEnergy_nonneg c s w ψ hw
  have hwpos : 0 ≤ (∑ i ∈ s, w i) + M :=
    add_nonneg (Finset.sum_nonneg hw) hM0
  nlinarith

/-- The same star bound expressed directly in the campaign's energy convention. -/
theorem weighted_star_energy_upper_bound {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (w : Fin n → ℝ) (ψ : Wave n) (M : ℝ)
    (hc : c ∉ s) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hM0 : 0 ≤ M) (hM : ∀ i ∈ s, w i ≤ M) (hψ : squaredNorm ψ = 1) :
    (∑ i ∈ s, w i / 2 * (∑ x, Complex.normSq
      (ψ x - ψ (x ∘ Equiv.swap c i)))) ≤ (∑ i ∈ s, w i) + M := by
  convert weighted_star_upper_bound c s w ψ M hc hw hM0 hM hψ using 1
  unfold starEnergy
  apply Finset.sum_congr rfl
  intro i hi
  rw [pairEnergy_eq]
  ring

end QuantumMaxCutEnergy.Star



-- Proof source: baseline/AnalyticProof.lean


noncomputable section
open scoped BigOperators
namespace QuantumMaxCutEnergy

def totalWeight {n : ℕ} (w : Weights n) : ℝ := ∑ e, (w e : ℝ)

lemma normSq_sub_bound (z v : ℂ) :
    Complex.normSq (z - v) ≤ 2 * Complex.normSq z + 2 * Complex.normSq v := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  nlinarith [sq_nonneg (z.re + v.re), sq_nonneg (z.im + v.im)]

def swapBasis {n : ℕ} (a b : Fin n) : Basis n ≃ Basis n where
  toFun x := x ∘ Equiv.swap a b
  invFun x := x ∘ Equiv.swap a b
  left_inv x := by funext i; simp [Function.comp_def]
  right_inv x := by funext i; simp [Function.comp_def]

lemma squaredNorm_swap_sum {n : ℕ} (ψ : Wave n) (a b : Fin n) :
    (∑ x, Complex.normSq (ψ (x ∘ Equiv.swap a b))) = squaredNorm ψ := by
  exact (swapBasis a b).sum_comp (fun x => Complex.normSq (ψ x))

lemma energy_nonnegative {n : ℕ} (w : Weights n)
    (ψ : Wave n) : 0 ≤ energy w ψ := by
  apply Finset.sum_nonneg
  intro e _
  apply mul_nonneg
  · positivity
  · exact Finset.sum_nonneg (fun x _ => Complex.normSq_nonneg _)

lemma energy_upper_bound {n : ℕ} (w : Weights n)
    (ψ : Wave n) :
    energy w ψ ≤ 2 * totalWeight w * squaredNorm ψ := by
  have edge_bound (a b : Fin n) :
      (∑ x, Complex.normSq (ψ x - ψ (x ∘ Equiv.swap a b))) ≤ 4 * squaredNorm ψ := by
    calc
      _ ≤ ∑ x, (2 * Complex.normSq (ψ x) +
            2 * Complex.normSq (ψ (x ∘ Equiv.swap a b))) :=
        Finset.sum_le_sum (fun x _ => normSq_sub_bound _ _)
      _ = 4 * squaredNorm ψ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          squaredNorm_swap_sum]
        unfold squaredNorm
        ring
  calc
    energy w ψ ≤ ∑ e, (w e : ℝ) / 2 * (4 * squaredNorm ψ) := by
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_left (edge_bound _ _) (by positivity)
    _ = ∑ e, (w e : ℝ) * (2 * squaredNorm ψ) := by
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = 2 * totalWeight w * squaredNorm ψ := by
      rw [← Finset.sum_mul]
      unfold totalWeight
      ring

end QuantumMaxCutEnergy

namespace QuantumMaxCutEnergy.BaselineSemantic

def ket {n : ℕ} (b : Basis n) : Wave n := fun x => if x = b then 1 else 0

def cutWeight {n : ℕ} (w : Weights n) (b : Basis n) : ℝ :=
  ∑ e, if b e.val.1 = b e.val.2 then 0 else (w e : ℝ)

lemma squaredNorm_ket {n : ℕ} (b : Basis n) : squaredNorm (ket b) = 1 := by
  classical
  simp [squaredNorm, ket]

lemma sum_delta_difference {α : Type} [Fintype α] [DecidableEq α] (a b : α) :
    (∑ x, Complex.normSq
      ((if x = a then (1 : ℂ) else 0) - (if x = b then (1 : ℂ) else 0))) =
      if a = b then 0 else 2 := by
  classical
  by_cases h : a = b
  · subst b
    simp
  · have hp : ∀ x, Complex.normSq
        ((if x = a then (1 : ℂ) else 0) - (if x = b then (1 : ℂ) else 0)) =
        (if x = a then (1 : ℝ) else 0) + (if x = b then (1 : ℝ) else 0) := by
      intro x
      by_cases ha : x = a
      · subst x
        simp [h]
      · by_cases hb : x = b
        · subst x
          simp [Ne.symm h]
        · simp [ha, hb]
    simp_rw [hp]
    rw [Finset.sum_add_distrib]
    norm_num [h]

lemma ket_swap {n : ℕ} (b x : Basis n) (i j : Fin n) :
    ket b (x ∘ Equiv.swap i j) = ket (b ∘ Equiv.swap i j) x := by
  classical
  have h : (x ∘ Equiv.swap i j = b) ↔ (x = b ∘ Equiv.swap i j) := by
    constructor <;> intro h
    · have hh := congrArg (fun f => f ∘ Equiv.swap i j) h
      simpa only [Function.comp_def, Equiv.swap_apply_self] using hh
    · subst x
      funext k
      simp [Function.comp_def]
  simp only [ket, h]

lemma eq_swap_iff {n : ℕ} (b : Basis n) (i j : Fin n) :
    (b = b ∘ Equiv.swap i j) ↔ b i = b j := by
  constructor
  · intro h
    simpa using congrFun h i
  · intro h
    funext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp_all [Equiv.swap_apply_def]

lemma pairEnergy_ket {n : ℕ} (b : Basis n) (i j : Fin n) :
    (∑ x, Complex.normSq (ket b x - ket b (x ∘ Equiv.swap i j))) =
      if b i = b j then 0 else 2 := by
  simp_rw [ket_swap]
  change (∑ x, Complex.normSq
    ((if x = b then (1 : ℂ) else 0) -
      (if x = b ∘ Equiv.swap i j then (1 : ℂ) else 0))) = _
  rw [sum_delta_difference]
  simp only [eq_swap_iff]

lemma energy_ket {n : ℕ} (w : Weights n) (b : Basis n) :
    energy w (ket b) = cutWeight w b := by
  classical
  unfold energy cutWeight
  apply Finset.sum_congr rfl
  intro e _
  change (w e : ℝ) / 2 *
    (∑ x, Complex.normSq (ket b x - ket b (x ∘ Equiv.swap e.val.1 e.val.2))) = _
  rw [pairEnergy_ket]
  split_ifs <;> ring

def flipBit {n : ℕ} (i : Fin n) (b : Basis n) : Basis n :=
  Function.update b i (!(b i))

lemma flipBit_involutive {n : ℕ} (i : Fin n) : Function.Involutive (flipBit i) := by
  intro b
  funext k
  by_cases hk : k = i
  · subst k
    simp [flipBit]
  · simp [flipBit, hk]

lemma uniform_cut_pair {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (∑ b : Basis n, if b i = b j then (0 : ℝ) else 1) =
      (Fintype.card (Basis n) : ℝ) / 2 := by
  classical
  let f : Basis n → ℝ := fun b => if b i = b j then 0 else 1
  have hflip (b : Basis n) : f (flipBit i b) = 1 - f b := by
    simp only [f, flipBit, Function.update_self,
      Function.update_of_ne (Ne.symm hij)]
    cases hi : b i <;> cases hj : b j <;> norm_num
  have hs : (∑ b, f b) = ∑ b : Basis n, (1 - f b) := by
    calc
      (∑ b, f b) = ∑ b, f (flipBit i b) :=
        ((flipBit_involutive i).bijective.sum_comp f).symm
      _ = _ := by simp_rw [hflip]
  rw [Finset.sum_sub_distrib] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
  change (∑ b, f b) = _
  linarith

lemma uniform_cut_sum {n : ℕ} (w : Weights n) :
    (∑ b : Basis n, cutWeight w b) =
      (Fintype.card (Basis n) : ℝ) / 2 * ∑ e, (w e : ℝ) := by
  classical
  unfold cutWeight
  rw [Finset.sum_comm]
  calc
    (∑ e, ∑ b : Basis n, if b e.val.1 = b e.val.2 then 0 else (w e : ℝ)) =
        ∑ e, (w e : ℝ) * ((Fintype.card (Basis n) : ℝ) / 2) := by
      apply Finset.sum_congr rfl
      intro e _
      have h := uniform_cut_pair e.val.1 e.val.2 (ne_of_lt e.property)
      rw [← h, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> ring
    _ = _ := by rw [← Finset.sum_mul]; ring

lemma uniform_basis_energy_sum {n : ℕ} (w : Weights n) :
    (∑ b : Basis n, energy w (ket b)) =
      (Fintype.card (Basis n) : ℝ) / 2 * ∑ e, (w e : ℝ) := by
  simp_rw [energy_ket]
  exact uniform_cut_sum w

def uniformBasisEnergy {n : ℕ} (w : Weights n) : ℝ :=
  (∑ b : Basis n, energy w (ket b)) /
    (Fintype.card (Basis n) : ℝ)

lemma uniformBasisEnergy_eq {n : ℕ} (w : Weights n) :
    uniformBasisEnergy w = (∑ e, (w e : ℝ)) / 2 := by
  have hcard : (Fintype.card (Basis n) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold uniformBasisEnergy
  rw [uniform_basis_energy_sum]
  field_simp

lemma uniformBasis_quarter_of_upper {n : ℕ} (w : Weights n) (ψ : Wave n)
    (hψ : squaredNorm ψ = 1)
    (hupper : energy w ψ ≤
      2 * (∑ e, (w e : ℝ)) * squaredNorm ψ) :
    (1 / 4 : ℝ) * energy w ψ ≤
      uniformBasisEnergy w := by
  rw [uniformBasisEnergy_eq]
  rw [hψ] at hupper
  linarith

end QuantumMaxCutEnergy.BaselineSemantic

namespace QuantumMaxCutEnergy

open BaselineSemantic

lemma energy_values_nonempty (G : Input) :
    {v : ℝ | ∃ ψ : Wave G.n, squaredNorm ψ = 1 ∧ v = energy G.weights ψ}.Nonempty := by
  refine ⟨_, _, squaredNorm_ket (fun _ => false), rfl⟩

lemma energy_values_bddAbove (G : Input) :
    BddAbove {v : ℝ | ∃ ψ : Wave G.n, squaredNorm ψ = 1 ∧ v = energy G.weights ψ} := by
  refine ⟨2 * totalWeight G.weights, ?_⟩
  rintro v ⟨ψ, hψ, rfl⟩
  simpa [hψ] using energy_upper_bound G.weights ψ

lemma energy_le_optimum (G : Input) (ψ : Wave G.n) (hψ : squaredNorm ψ = 1) :
    energy G.weights ψ ≤ optimum G := by
  exact le_csSup (energy_values_bddAbove G) ⟨ψ, hψ, rfl⟩

lemma optimum_le_two_totalWeight (G : Input) :
    optimum G ≤ 2 * totalWeight G.weights := by
  apply csSup_le (energy_values_nonempty G)
  rintro v ⟨ψ, hψ, rfl⟩
  simpa [hψ] using energy_upper_bound G.weights ψ

lemma half_totalWeight_le_optimum (G : Input) :
    totalWeight G.weights / 2 ≤ optimum G := by
  have hcard : (0 : ℝ) < (Fintype.card (Basis G.n) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have havg : uniformBasisEnergy G.weights ≤ optimum G := by
    unfold uniformBasisEnergy
    apply (div_le_iff₀ hcard).2
    calc
      (∑ b : Basis G.n, energy G.weights (ket b)) ≤
          ∑ _b : Basis G.n, optimum G := by
        exact Finset.sum_le_sum (fun b _ => energy_le_optimum G (ket b) (squaredNorm_ket b))
      _ = optimum G * (Fintype.card (Basis G.n) : ℝ) := by
        simp [mul_comm]
  simpa [uniformBasisEnergy_eq, totalWeight] using havg

lemma quarter_optimum_le_half_totalWeight (G : Input) :
    (0.25 : ℝ) * optimum G ≤ totalWeight G.weights / 2 := by
  have h := optimum_le_two_totalWeight G
  linarith

def quarterValue (G : Input) : ℚ≥0 := (∑ e, G.weights e) / 2

lemma quarterValue_cast (G : Input) :
    (quarterValue G : ℝ) = totalWeight G.weights / 2 := by
  simp [quarterValue, totalWeight, NNRat.cast_sum]

def quarterEstimator : Algorithm where
  randomFactor := 0
  randomDegree := 0
  run G _ := quarterValue G

theorem quarterEstimator_ratio : ApproximationRatio quarterEstimator (0.25 : ℝ) := by
  intro G
  constructor
  · intro r
    simpa [quarterEstimator, quarterValue_cast] using half_totalWeight_le_optimum G
  · have hcard : (Fintype.card (Fin (randomBits quarterEstimator G) → Bool) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    change (0.25 : ℝ) * optimum G ≤
      (∑ _r : Fin (randomBits quarterEstimator G) → Bool, (quarterValue G : ℝ)) /
        (Fintype.card (Fin (randomBits quarterEstimator G) → Bool) : ℝ)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_div_cancel_left₀ _ hcard]
    simpa only [quarterValue_cast] using quarter_optimum_le_half_totalWeight G


end QuantumMaxCutEnergy




-- Proof source: baseline/next-half/StarCover.lean


noncomputable section
namespace QuantumMaxCutEnergy.Star

lemma pairEnergy_comm {n : ℕ} (i j : Fin n) (ψ : Wave n) :
    pairEnergy i j ψ = pairEnergy j i ψ := by
  have hs : swapWave i j ψ = swapWave j i ψ := by
    funext x
    simp only [swapWave, Equiv.swap_comm i j]
  simp only [pairEnergy, edgeAction, hs]

@[simp] lemma pairEnergy_self {n : ℕ} (i : Fin n) (ψ : Wave n) :
    pairEnergy i i ψ = 0 := by
  have hs : swapWave i i ψ = ψ := by
    funext x
    simp [swapWave]
  simp [pairEnergy, edgeAction, hs]

lemma energy_eq_pairEnergy {n : ℕ} (w : Weights n) (ψ : Wave n) :
    energy w ψ = ∑ e, (w e : ℝ) * pairEnergy e.val.1 e.val.2 ψ := by
  unfold energy
  apply Finset.sum_congr rfl
  intro e he
  rw [pairEnergy_eq]
  ring

lemma sum_ordered_pairs {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, if i < j then f i j else 0) =
      ∑ e : Edge n, f e.val.1 e.val.2 := by
  classical
  let g : Fin n × Fin n → ℝ := fun p => if p.1 < p.2 then f p.1 p.2 else 0
  have hg : (∑ p, g p) = ∑ e : Edge n, f e.val.1 e.val.2 := by
    apply Finset.sum_congr_set {p : Fin n × Fin n | p.1 < p.2} g
      (fun e : Edge n => f e.val.1 e.val.2)
    · intro p hp
      change p.1 < p.2 at hp
      simp only [g, if_pos hp]
    · intro p hp
      change ¬p.1 < p.2 at hp
      simp only [g, if_neg hp]
  simpa only [Fintype.sum_prod_type, g] using hg

lemma sum_off_diagonal {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = ∑ e : Edge n,
      (f e.val.1 e.val.2 + f e.val.2 e.val.1) := by
  classical
  have hsplit : (∑ i, ∑ j, f i j) =
      (∑ i, ∑ j, if i < j then f i j else 0) +
        ∑ i, ∑ j, if j < i then f i j else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j
      simp [hdiag]
    · simp [h, not_lt_of_gt h]
  rw [hsplit]
  conv_lhs => arg 2; rw [Finset.sum_comm]
  rw [sum_ordered_pairs, sum_ordered_pairs, ← Finset.sum_add_distrib]

lemma oriented_totalWeight {n : ℕ} (w : Weights n) (v : Fin n → Fin n → ℝ)
    (hdiag : ∀ i, v i i = 0)
    (hparts : ∀ e : Edge n, v e.val.1 e.val.2 + v e.val.2 e.val.1 = (w e : ℝ)) :
    (∑ c, ∑ i ∈ Finset.univ.erase c, v c i) = totalWeight w := by
  classical
  have hrow (c : Fin n) : (∑ i ∈ Finset.univ.erase c, v c i) = ∑ i, v c i :=
    Finset.sum_erase Finset.univ (hdiag c)
  simp only [hrow]
  rw [sum_off_diagonal v hdiag]
  exact Finset.sum_congr rfl fun e he => hparts e

lemma oriented_energy {n : ℕ} (w : Weights n) (v : Fin n → Fin n → ℝ)
    (hparts : ∀ e : Edge n, v e.val.1 e.val.2 + v e.val.2 e.val.1 = (w e : ℝ))
    (ψ : Wave n) :
    (∑ c, starEnergy c (Finset.univ.erase c) (v c) ψ) = energy w ψ := by
  classical
  unfold starEnergy
  have hrow (c : Fin n) :
      (∑ i ∈ Finset.univ.erase c, v c i * pairEnergy c i ψ) =
        ∑ i, v c i * pairEnergy c i ψ :=
    Finset.sum_erase Finset.univ (by simp)
  simp only [hrow]
  rw [sum_off_diagonal (fun i j => v i j * pairEnergy i j ψ) (by simp),
    energy_eq_pairEnergy]
  apply Finset.sum_congr rfl
  intro e he
  rw [pairEnergy_comm e.val.2 e.val.1 ψ, ← add_mul, hparts e]

/-- Any orientation of the edges into bounded weighted stars certifies an upper
bound on the full graph energy. -/
theorem energy_le_star_cover {n : ℕ} (w : Weights n)
    (v : Fin n → Fin n → ℝ) (M : Fin n → ℝ)
    (hdiag : ∀ i, v i i = 0)
    (hparts : ∀ e : Edge n, v e.val.1 e.val.2 + v e.val.2 e.val.1 = (w e : ℝ))
    (hv : ∀ c i, 0 ≤ v c i) (hM0 : ∀ c, 0 ≤ M c)
    (hM : ∀ c i, c ≠ i → v c i ≤ M c)
    (ψ : Wave n) (hψ : squaredNorm ψ = 1) :
    energy w ψ ≤ totalWeight w + ∑ c, M c := by
  classical
  rw [← oriented_energy w v hparts ψ]
  calc
    _ ≤ ∑ c, ((∑ i ∈ Finset.univ.erase c, v c i) + M c) := by
      apply Finset.sum_le_sum
      intro c hc
      apply weighted_star_upper_bound c (Finset.univ.erase c) (v c) ψ (M c)
      · simp
      · exact fun i hi => hv c i
      · exact hM0 c
      · intro i hi
        exact hM c i (Finset.ne_of_mem_erase hi).symm
      · exact hψ
    _ = _ := by rw [Finset.sum_add_distrib, oriented_totalWeight w v hdiag hparts]

theorem optimum_le_star_cover {n : ℕ} (w : Weights n)
    (v : Fin n → Fin n → ℝ) (M : Fin n → ℝ)
    (hdiag : ∀ i, v i i = 0)
    (hparts : ∀ e : Edge n, v e.val.1 e.val.2 + v e.val.2 e.val.1 = (w e : ℝ))
    (hv : ∀ c i, 0 ≤ v c i) (hM0 : ∀ c, 0 ≤ M c)
    (hM : ∀ c i, c ≠ i → v c i ≤ M c) :
    optimum ⟨n, w⟩ ≤ totalWeight w + ∑ c, M c := by
  apply csSup_le (energy_values_nonempty ⟨n, w⟩)
  intro b hb
  rcases hb with ⟨ψ, hψ, rfl⟩
  exact energy_le_star_cover w v M hdiag hparts hv hM0 hM ψ hψ

end QuantumMaxCutEnergy.Star



-- Proof source: baseline/next-half/PriceCover.lean


noncomputable section
namespace QuantumMaxCutEnergy.Star

/-- Assign each edge to its endpoint with the larger price, resolving ties by
the vertex order. This definition is only a mathematical upper-bound witness. -/
def priceOrientation {n : ℕ} (w : Weights n) (p : Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  if hij : i < j then
    if p j ≤ p i then (w ⟨(i, j), hij⟩ : ℝ) else 0
  else if hji : j < i then
    if p j < p i then (w ⟨(j, i), hji⟩ : ℝ) else 0
  else 0

lemma priceOrientation_diag {n : ℕ} (w : Weights n) (p : Fin n → ℝ) (i : Fin n) :
    priceOrientation w p i i = 0 := by
  simp [priceOrientation]

lemma priceOrientation_parts {n : ℕ} (w : Weights n) (p : Fin n → ℝ) (e : Edge n) :
    priceOrientation w p e.val.1 e.val.2 + priceOrientation w p e.val.2 e.val.1 =
      (w e : ℝ) := by
  have hij := e.property
  have hji : ¬e.val.2 < e.val.1 := not_lt_of_gt hij
  have he : (⟨(e.val.1, e.val.2), hij⟩ : Edge n) = e := by
    cases e
    rfl
  by_cases hp : p e.val.2 ≤ p e.val.1
  · simp [priceOrientation, hij, hji, hp, not_lt.mpr hp, he]
  · simp [priceOrientation, hij, hji, hp, lt_of_not_ge hp, he]

lemma priceOrientation_nonneg {n : ℕ} (w : Weights n) (p : Fin n → ℝ) (i j : Fin n) :
    0 ≤ priceOrientation w p i j := by
  unfold priceOrientation
  split_ifs <;> positivity

lemma priceOrientation_le {n : ℕ} (w : Weights n) (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hcover : ∀ e : Edge n, (w e : ℝ) ≤ max (p e.val.1) (p e.val.2))
    (i j : Fin n) :
    priceOrientation w p i j ≤ p i := by
  unfold priceOrientation
  split_ifs with hij hprice hji hprice
  · simpa only [max_eq_left hprice] using hcover ⟨(i, j), hij⟩
  · exact hp i
  · simpa only [max_eq_right hprice.le] using hcover ⟨(j, i), hji⟩
  · exact hp i
  · exact hp i

/-- If every edge is bounded by the larger of its endpoint prices, the QMC
optimum is bounded by the total graph weight plus the sum of those prices. -/
theorem optimum_le_price_cover {n : ℕ} (w : Weights n) (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hcover : ∀ e : Edge n, (w e : ℝ) ≤ max (p e.val.1) (p e.val.2)) :
    optimum ⟨n, w⟩ ≤ totalWeight w + ∑ i, p i := by
  apply optimum_le_star_cover w (priceOrientation w p) p
  · exact priceOrientation_diag w p
  · exact priceOrientation_parts w p
  · exact priceOrientation_nonneg w p
  · exact hp
  · intro i j hij
    exact priceOrientation_le w p hp hcover i j

end QuantumMaxCutEnergy.Star



-- Proof source: baseline/next-half/GreedyCover.lean


noncomputable section
namespace QuantumMaxCutEnergy.Star

def endpoints {n : ℕ} (e : Edge n) : Finset (Fin n) := {e.val.1, e.val.2}

def IsMatching {n : ℕ} (m : Finset (Edge n)) : Prop :=
  ∀ e ∈ m, ∀ f ∈ m, e ≠ f → Disjoint (endpoints e) (endpoints f)

def matchingPrice {n : ℕ} (w : Weights n) (m : Finset (Edge n)) (i : Fin n) : ℝ :=
  ∑ e ∈ m, if i ∈ endpoints e then (w e : ℝ) else 0

lemma matchingPrice_nonneg {n : ℕ} (w : Weights n) (m : Finset (Edge n)) (i : Fin n) :
    0 ≤ matchingPrice w m i := by
  apply Finset.sum_nonneg
  intro e he
  split_ifs <;> positivity

lemma matchingPrice_insert {n : ℕ} (w : Weights n) (m : Finset (Edge n))
    (e : Edge n) (he : e ∉ m) (i : Fin n) :
    matchingPrice w (insert e m) i =
      (if i ∈ endpoints e then (w e : ℝ) else 0) + matchingPrice w m i := by
  simp only [matchingPrice, Finset.sum_insert he]

lemma matchingPrice_mono_insert {n : ℕ} (w : Weights n) (m : Finset (Edge n))
    (e : Edge n) (he : e ∉ m) (i : Fin n) :
    matchingPrice w m i ≤ matchingPrice w (insert e m) i := by
  rw [matchingPrice_insert w m e he i]
  have h : 0 ≤ if i ∈ endpoints e then (w e : ℝ) else 0 := by
    split_ifs <;> positivity
  linarith

lemma matchingPrice_sum {n : ℕ} (w : Weights n) (m : Finset (Edge n)) :
    (∑ i, matchingPrice w m i) = 2 * ∑ e ∈ m, (w e : ℝ) := by
  classical
  unfold matchingPrice
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hne : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  calc
    _ = ∑ i, ((if i = e.val.1 then (w e : ℝ) else 0) +
        if i = e.val.2 then (w e : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [endpoints, Finset.mem_insert, Finset.mem_singleton]
      by_cases hi1 : i = e.val.1 <;> by_cases hi2 : i = e.val.2 <;>
        simp_all
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp [two_mul]

/-- Greedy selection of a maximum-weight remaining edge produces a matching
whose endpoint prices dominate every edge in the original finite set. -/
theorem exists_greedy_cover {n : ℕ} (w : Weights n) (E : Finset (Edge n)) :
    ∃ m : Finset (Edge n), m ⊆ E ∧ IsMatching m ∧
      ∀ f ∈ E, (w f : ℝ) ≤
        max (matchingPrice w m f.val.1) (matchingPrice w m f.val.2) := by
  classical
  induction E using Finset.strongInductionOn with
  | _ E ih =>
    by_cases hE : E.Nonempty
    · obtain ⟨e, he, hmax⟩ := E.exists_max_image (fun e => (w e : ℝ)) hE
      let R := E.filter (fun f => Disjoint (endpoints e) (endpoints f))
      have hRsub : R ⊆ E := Finset.filter_subset _ _
      have heR : e ∉ R := by
        intro h
        have hd := (Finset.mem_filter.mp h).2
        have hi : e.val.1 ∈ endpoints e := by simp [endpoints]
        exact Finset.disjoint_left.mp hd hi hi
      have hRlt : R ⊂ E := Finset.ssubset_iff_subset_ne.mpr ⟨hRsub, by
        intro h
        exact heR (h ▸ he)⟩
      obtain ⟨m, hm, hmatch, hcover⟩ := ih R hRlt
      have hem : e ∉ m := fun h => heR (hm h)
      refine ⟨insert e m, ?_, ?_, ?_⟩
      · exact Finset.insert_subset_iff.mpr ⟨he, fun f hf => hRsub (hm hf)⟩
      · intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with hae | ham
        · subst a
          rcases Finset.mem_insert.mp hb with hbe | hbm
          · exact False.elim (hab hbe.symm)
          · exact (Finset.mem_filter.mp (hm hbm)).2
        · rcases Finset.mem_insert.mp hb with hbe | hbm
          · subst b
            exact (Finset.mem_filter.mp (hm ham)).2.symm
          · exact hmatch a ham b hbm hab
      · intro f hf
        by_cases hfR : f ∈ R
        · exact (hcover f hfR).trans (max_le_max
            (matchingPrice_mono_insert w m e hem f.val.1)
            (matchingPrice_mono_insert w m e hem f.val.2))
        · have hnot : ¬Disjoint (endpoints e) (endpoints f) := by
            intro h
            exact hfR (Finset.mem_filter.mpr ⟨hf, h⟩)
          obtain ⟨i, hie, hif⟩ := Finset.not_disjoint_iff.mp hnot
          have hp : (w e : ℝ) ≤ matchingPrice w (insert e m) i := by
            rw [matchingPrice_insert w m e hem i, if_pos hie]
            exact le_add_of_nonneg_right (matchingPrice_nonneg w m i)
          have hbound := (hmax f hf).trans hp
          simp only [endpoints, Finset.mem_insert, Finset.mem_singleton] at hif
          rcases hif with rfl | rfl
          · exact hbound.trans (le_max_left _ _)
          · exact hbound.trans (le_max_right _ _)
    · refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
      · simp [IsMatching]
      · intro f hf
        exact False.elim (hE ⟨f, hf⟩)

theorem exists_matching_optimum_upper_bound {n : ℕ} (w : Weights n) :
    ∃ m : Finset (Edge n), IsMatching m ∧
      optimum ⟨n, w⟩ ≤ totalWeight w + 2 * ∑ e ∈ m, (w e : ℝ) := by
  classical
  obtain ⟨m, hm, hmatch, hcover⟩ := exists_greedy_cover w Finset.univ
  refine ⟨m, hmatch, ?_⟩
  have h := optimum_le_price_cover w (matchingPrice w m)
    (matchingPrice_nonneg w m) (fun e => hcover e (Finset.mem_univ e))
  rwa [matchingPrice_sum] at h

end QuantumMaxCutEnergy.Star



-- Proof source: published-agm/IncidentDecomposition.lean


/-!
Published source: Anshu, Gosset, Morenz, TQC 2020,
doi:10.4230/LIPIcs.TQC.2020.7, Lemma 7, pp. 7:9–7:10.
This file isolates the matching and weight-identity part of that lemma.
It does not yet claim that the selected-edge set is a forest, or a runtime bound.
-/

noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.PublishedAGM.Incident
open QuantumMaxCutEnergy.Star

def selectedEdges {n : ℕ} (E : Finset (Edge n)) (I : Fin n → Option (Edge n)) :
    Finset (Edge n) := E.filter (fun e => ∃ v, I v = some e)

def mutualEdges {n : ℕ} (E : Finset (Edge n)) (I : Fin n → Option (Edge n)) :
    Finset (Edge n) := E.filter (fun e => I e.val.1 = some e ∧ I e.val.2 = some e)

def selectedWeight {n : ℕ} (w : Weights n) (I : Fin n → Option (Edge n))
    (v : Fin n) : ℝ := (I v).elim 0 (fun e => (w e : ℝ))

def ValidSelector {n : ℕ} (E : Finset (Edge n)) (I : Fin n → Option (Edge n)) : Prop :=
  ∀ v e, I v = some e → e ∈ E ∧ v ∈ endpoints e

lemma mutual_selected_at {n : ℕ} (E : Finset (Edge n)) (I : Fin n → Option (Edge n))
    (e : Edge n) (he : e ∈ mutualEdges E I) (v : Fin n) (hv : v ∈ endpoints e) :
    I v = some e := by
  have h := (Finset.mem_filter.mp he).2
  simp only [endpoints, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact h.1
  · exact h.2

theorem mutual_isMatching {n : ℕ} (E : Finset (Edge n))
    (I : Fin n → Option (Edge n)) : IsMatching (mutualEdges E I) := by
  intro e he f hf hef
  apply Finset.disjoint_left.mpr
  intro v hve hvf
  have h := (mutual_selected_at E I e he v hve).symm.trans
    (mutual_selected_at E I f hf v hvf)
  exact hef (Option.some.inj h)

lemma mutual_subset_selected {n : ℕ} (E : Finset (Edge n))
    (I : Fin n → Option (Edge n)) : mutualEdges E I ⊆ selectedEdges E I := by
  intro e he
  have h := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨h.1, e.val.1, h.2.1⟩

lemma selected_iff_endpoints {n : ℕ} (E : Finset (Edge n))
    (I : Fin n → Option (Edge n)) (hI : ValidSelector E I) (e : Edge n) :
    (∃ v, I v = some e) ↔ I e.val.1 = some e ∨ I e.val.2 = some e := by
  constructor
  · rintro ⟨v, hv⟩
    have hinc := (hI v e hv).2
    simp only [endpoints, Finset.mem_insert, Finset.mem_singleton] at hinc
    rcases hinc with rfl | rfl
    · exact Or.inl hv
    · exact Or.inr hv
  · rintro (h | h)
    · exact ⟨e.val.1, h⟩
    · exact ⟨e.val.2, h⟩

lemma selectedWeight_eq_sum {n : ℕ} (E : Finset (Edge n)) (w : Weights n)
    (I : Fin n → Option (Edge n)) (hI : ValidSelector E I) (v : Fin n) :
    selectedWeight w I v = ∑ e ∈ E, if I v = some e then (w e : ℝ) else 0 := by
  classical
  cases hv : I v with
  | none => simp [selectedWeight, hv]
  | some e =>
      have he := (hI v e hv).1
      simp [selectedWeight, hv, he]

lemma selected_edge_multiplicity {n : ℕ} (E : Finset (Edge n)) (w : Weights n)
    (I : Fin n → Option (Edge n)) (hI : ValidSelector E I) (e : Edge n) :
    (∑ v, if I v = some e then (w e : ℝ) else 0) =
      (if I e.val.1 = some e then (w e : ℝ) else 0) +
      (if I e.val.2 = some e then (w e : ℝ) else 0) := by
  classical
  have hrestrict : (∑ v ∈ endpoints e, if I v = some e then (w e : ℝ) else 0) =
      ∑ v, if I v = some e then (w e : ℝ) else 0 := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    have hnot : I v ≠ some e := by
      intro h
      exact hv (hI v e h).2
    simp [hnot]
  rw [← hrestrict]
  unfold endpoints
  rw [Finset.sum_insert (by simpa using (ne_of_lt e.property)), Finset.sum_singleton]

/-- The exact double-counting identity in the proof of published Lemma 7.
Acyclicity of selectedEdges requires the additional global ordering condition. -/
theorem incident_weight_identity {n : ℕ} (E : Finset (Edge n)) (w : Weights n)
    (I : Fin n → Option (Edge n)) (hI : ValidSelector E I) :
    (∑ v, selectedWeight w I v) =
      (∑ e ∈ mutualEdges E I, (w e : ℝ)) +
      ∑ e ∈ selectedEdges E I, (w e : ℝ) := by
  classical
  simp_rw [selectedWeight_eq_sum E w I hI]
  rw [Finset.sum_comm]
  simp_rw [selected_edge_multiplicity E w I hI]
  simp only [mutualEdges, selectedEdges, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  simp only [selected_iff_endpoints E I hI e]
  by_cases hl : I e.val.1 = some e <;> by_cases hr : I e.val.2 = some e <;>
    simp [hl, hr, two_mul]

def incidentEdges {n : ℕ} (E : Finset (Edge n)) (v : Fin n) : Finset (Edge n) :=
  E.filter (fun e => v ∈ endpoints e)

def maximumIncident {n : ℕ} (E : Finset (Edge n)) (w : Weights n)
    (v : Fin n) : Option (Edge n) :=
  if h : (incidentEdges E v).Nonempty then
    some (Classical.choose ((incidentEdges E v).exists_max_image w h))
  else none

theorem maximumIncident_valid {n : ℕ} (E : Finset (Edge n)) (w : Weights n) :
    ValidSelector E (maximumIncident E w) := by
  intro v e he
  unfold maximumIncident at he
  split_ifs at he with h
  · have hm := Classical.choose_spec ((incidentEdges E v).exists_max_image w h)
    have heq := Option.some.inj he
    subst e
    exact Finset.mem_filter.mp hm.1

theorem maximumIncident_max {n : ℕ} (E : Finset (Edge n)) (w : Weights n)
    (v : Fin n) (e : Edge n) (he : e ∈ E) (hv : v ∈ endpoints e) :
    (w e : ℝ) ≤ selectedWeight w (maximumIncident E w) v := by
  have he' : e ∈ incidentEdges E v := Finset.mem_filter.mpr ⟨he, hv⟩
  have hn : (incidentEdges E v).Nonempty := ⟨e, he'⟩
  have hm := Classical.choose_spec ((incidentEdges E v).exists_max_image w hn)
  simp only [selectedWeight, maximumIncident, dif_pos hn, Option.elim_some]
  exact_mod_cast hm.2 e he'


end QuantumMaxCutEnergy.PublishedAGM.Incident



-- Proof source: published-agm/IncidentForest.lean


noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.PublishedAGM.Incident
open QuantumMaxCutEnergy.Star

def edgeGraph {n : ℕ} (F : Finset (Edge n)) : SimpleGraph (Fin n) :=
  ⨆ e ∈ F, SimpleGraph.edge e.val.1 e.val.2

@[simp] lemma edgeGraph_empty (n : ℕ) : edgeGraph (∅ : Finset (Edge n)) = ⊥ := by
  simp [edgeGraph]

lemma edgeGraph_insert {n : ℕ} (e : Edge n) (F : Finset (Edge n)) :
    edgeGraph (insert e F) = edgeGraph F ⊔ SimpleGraph.edge e.val.1 e.val.2 := by
  ext a b
  simp [edgeGraph, SimpleGraph.iSup_adj, or_comm, or_left_comm, or_assoc]

lemma edgeGraph_adj_endpoint {n : ℕ} (F : Finset (Edge n)) (v u : Fin n)
    (h : (edgeGraph F).Adj v u) : ∃ e ∈ F, v ∈ endpoints e := by
  simp only [edgeGraph, SimpleGraph.iSup_adj, exists_prop] at h
  obtain ⟨e, he, hadj⟩ := h
  refine ⟨e, he, ?_⟩
  rcases (SimpleGraph.edge_adj e.val.1 e.val.2 v u).mp hadj with ⟨h | h, _⟩
  · simp [endpoints, h.1]
  · simp [endpoints, h.1]

lemma edgeGraph_isolated {n : ℕ} (F : Finset (Edge n)) (v : Fin n)
    (hv : ∀ e ∈ F, v ∉ endpoints e) : (edgeGraph F).neighborSet v = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro u hu
  obtain ⟨e, he, hve⟩ := edgeGraph_adj_endpoint F v u hu
  exact hv e he hve

/-- Global tie breaking is essential: local maximum choices can create cycles
when several incident weights tie. Injective priorities prevent that issue. -/
theorem selectedEdges_isAcyclic {n : ℕ} {β : Type*} [LinearOrder β]
    (E : Finset (Edge n)) (I : Fin n → Option (Edge n)) (hI : ValidSelector E I)
    (priority : Edge n → β) (hinj : Function.Injective priority)
    (hmax : ∀ v e, I v = some e → ∀ f ∈ E, v ∈ endpoints f → priority f ≤ priority e) :
    (edgeGraph (selectedEdges E I)).IsAcyclic := by
  classical
  suffices h : ∀ F : Finset (Edge n), F ⊆ selectedEdges E I → (edgeGraph F).IsAcyclic by
    exact h _ (Finset.Subset.refl _)
  intro F
  induction F using Finset.strongInductionOn with
  | _ F ih =>
    intro hF
    by_cases hne : F.Nonempty
    · obtain ⟨e, he, hmin⟩ := F.exists_min_image priority hne
      obtain ⟨v, hv⟩ := (Finset.mem_filter.mp (hF he)).2
      have hve := (hI v e hv).2
      have hfresh : ∀ f ∈ F.erase e, v ∉ endpoints f := by
        intro f hf hvf
        have hfm := (Finset.mem_erase.mp hf).2
        have hfe := (Finset.mem_filter.mp (hF hfm)).1
        have hle := hmax v e hv f hfe hvf
        have hge := hmin f hfm
        exact (Finset.mem_erase.mp hf).1 (hinj (le_antisymm hle hge))
      have hacyc := ih (F.erase e) (Finset.erase_ssubset he)
        (fun f hf => hF (Finset.mem_erase.mp hf).2)
      have hnr : ¬(edgeGraph (F.erase e)).Reachable e.val.1 e.val.2 := by
        have hi := edgeGraph_isolated (F.erase e) v hfresh
        simp only [endpoints, Finset.mem_insert, Finset.mem_singleton] at hve
        rcases hve with rfl | rfl
        · exact SimpleGraph.not_reachable_of_neighborSet_left_eq_empty
            (ne_of_lt e.property) hi
        · exact SimpleGraph.not_reachable_of_neighborSet_right_eq_empty
            (ne_of_lt e.property) hi
      have heq : F = insert e (F.erase e) := (Finset.insert_erase he).symm
      rw [heq, edgeGraph_insert]
      exact hacyc.sup_edge_of_not_reachable hnr
    · have hz : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [hz]

def rankIncident {n : ℕ} {β : Type*} [LinearOrder β]
    (E : Finset (Edge n)) (priority : Edge n → β) (v : Fin n) : Option (Edge n) :=
  if h : (incidentEdges E v).Nonempty then
    some (Classical.choose ((incidentEdges E v).exists_max_image priority h))
  else none

lemma rankIncident_valid {n : ℕ} {β : Type*} [LinearOrder β]
    (E : Finset (Edge n)) (priority : Edge n → β) :
    ValidSelector E (rankIncident E priority) := by
  intro v e he
  unfold rankIncident at he
  split_ifs at he with h
  have hm := Classical.choose_spec ((incidentEdges E v).exists_max_image priority h)
  have heq := Option.some.inj he
  subst e
  exact Finset.mem_filter.mp hm.1

lemma rankIncident_max {n : ℕ} {β : Type*} [LinearOrder β]
    (E : Finset (Edge n)) (priority : Edge n → β) (v : Fin n) (e : Edge n)
    (he : rankIncident E priority v = some e) (f : Edge n)
    (hf : f ∈ E) (hv : v ∈ endpoints f) : priority f ≤ priority e := by
  have hf' : f ∈ incidentEdges E v := Finset.mem_filter.mpr ⟨hf, hv⟩
  have hn : (incidentEdges E v).Nonempty := ⟨f, hf'⟩
  have hm := Classical.choose_spec ((incidentEdges E v).exists_max_image priority hn)
  simp only [rankIncident, dif_pos hn, Option.some.injEq] at he
  rw [← he]
  exact hm.2 f hf'

def weightPriority {n : ℕ} (w : Weights n) (e : Edge n) : ℚ≥0 ×ₗ (ℕ ×ₗ ℕ) :=
  toLex (w e, toLex (e.val.1.val, e.val.2.val))

lemma weightPriority_injective {n : ℕ} (w : Weights n) :
    Function.Injective (weightPriority w) := by
  intro e f h
  have hpair : (e.val.1.val, e.val.2.val) = (f.val.1.val, f.val.2.val) :=
    congrArg (fun x : ℚ≥0 ×ₗ (ℕ ×ₗ ℕ) => ofLex (ofLex x).2) h
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.ext (congrArg Prod.fst hpair)
  · exact Fin.ext (congrArg Prod.snd hpair)

lemma weight_le_of_priority {n : ℕ} (w : Weights n) (e f : Edge n)
    (h : weightPriority w e ≤ weightPriority w f) : w e ≤ w f := by
  rcases Prod.Lex.toLex_le_toLex.mp h with hl | ⟨he, _⟩
  · exact hl.le
  · exact he.le


end QuantumMaxCutEnergy.PublishedAGM.Incident



-- Proof source: published-agm/IncidentLemma7.lean


/-!
The complete finite combinatorial content of published TQC2020 Lemma 7,
pp. 7:9–7:10. The theorem includes actual Mathlib graph acyclicity.
It does not assert the paper's efficient-computation claim.
-/

noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.PublishedAGM.Incident
open QuantumMaxCutEnergy.Star

def incidentMaximum {n : ℕ} (E : Finset (Edge n)) (w : Weights n) (v : Fin n) : ℚ≥0 :=
  (incidentEdges E v).sup w

lemma rankIncident_weight_eq_max {n : ℕ} (E : Finset (Edge n)) (w : Weights n)
    (v : Fin n) :
    selectedWeight w (rankIncident E (weightPriority w)) v = (incidentMaximum E w v : ℝ) := by
  classical
  by_cases h : (incidentEdges E v).Nonempty
  · have hm := Classical.choose_spec
      ((incidentEdges E v).exists_max_image (weightPriority w) h)
    let e := Classical.choose ((incidentEdges E v).exists_max_image (weightPriority w) h)
    have hemax : ∀ f ∈ incidentEdges E v, w f ≤ w e := by
      intro f hf
      exact weight_le_of_priority w f e (hm.2 f hf)
    have heq : incidentMaximum E w v = w e :=
      le_antisymm (Finset.sup_le hemax) (Finset.le_sup hm.1)
    simp only [selectedWeight, rankIncident, dif_pos h, Option.elim_some, heq]
    rfl
  · have he : incidentEdges E v = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [selectedWeight, rankIncident, h, incidentMaximum, he]

theorem exists_incident_matching_forest {n : ℕ} (E : Finset (Edge n)) (w : Weights n) :
    ∃ M F : Finset (Edge n), M ⊆ E ∧ F ⊆ E ∧ M ⊆ F ∧ IsMatching M ∧
      (edgeGraph F).IsAcyclic ∧
      (∑ v, (incidentMaximum E w v : ℝ)) =
        (∑ e ∈ M, (w e : ℝ)) + ∑ e ∈ F, (w e : ℝ) := by
  classical
  let I := rankIncident E (weightPriority w)
  have hI : ValidSelector E I := rankIncident_valid E (weightPriority w)
  refine ⟨mutualEdges E I, selectedEdges E I, Finset.filter_subset _ _,
    Finset.filter_subset _ _, mutual_subset_selected E I, mutual_isMatching E I, ?_, ?_⟩
  · exact selectedEdges_isAcyclic E I hI (weightPriority w) (weightPriority_injective w)
      (rankIncident_max E (weightPriority w))
  · have hid := incident_weight_identity E w I hI
    simpa only [I, rankIncident_weight_eq_max] using hid

/-- A formulation using only the campaign's input types and Mathlib graph
acyclicity, suitable as a public theorem without additional definitions. -/
theorem published_lemma7_combinatorial {n : ℕ} (E : Finset (Edge n)) (w : Weights n) :
    ∃ M F : Finset (Edge n), M ⊆ E ∧ F ⊆ E ∧ M ⊆ F ∧
      (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint
        ({e.val.1, e.val.2} : Finset (Fin n)) {f.val.1, f.val.2}) ∧
      (⨆ e ∈ F, SimpleGraph.edge e.val.1 e.val.2).IsAcyclic ∧
      (∑ v, (((E.filter (fun e => v = e.val.1 ∨ v = e.val.2)).sup w : ℚ≥0) : ℝ)) =
        (∑ e ∈ M, (w e : ℝ)) + ∑ e ∈ F, (w e : ℝ) := by
  simpa only [IsMatching, endpoints, edgeGraph, incidentMaximum, incidentEdges,
    Finset.mem_insert, Finset.mem_singleton] using exists_incident_matching_forest E w


end QuantumMaxCutEnergy.PublishedAGM.Incident



-- Proof source: published-agm/ForestCutWitness.lean


/-!
Published source: Anshu, Gosset, Morenz, TQC 2020,
doi:10.4230/LIPIcs.TQC.2020.7, Eq. (26), p. 7:10.
Every forest has a computational-basis state whose QMC energy is at least
the forest's total weight. This file proves existence, not runtime.
-/

noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.PublishedAGM
open QuantumMaxCutEnergy.Star
open QuantumMaxCutEnergy.BaselineSemantic
open Incident

theorem forest_has_cut {n : ℕ} (F : Finset (Edge n)) (hF : (edgeGraph F).IsAcyclic) :
    ∃ b : Basis n, ∀ e ∈ F, b e.val.1 ≠ b e.val.2 := by
  let C := hF.coloringTwo
  refine ⟨fun v => finTwoEquiv (C v), ?_⟩
  intro e he hsame
  have hadj : (edgeGraph F).Adj e.val.1 e.val.2 := by
    simp only [edgeGraph, SimpleGraph.iSup_adj, exists_prop]
    refine ⟨e, he, ?_⟩
    simp [SimpleGraph.edge_adj, ne_of_lt e.property]
  exact C.valid hadj (finTwoEquiv.injective hsame)

theorem forest_energy_lower {n : ℕ} (F : Finset (Edge n)) (w : Weights n)
    (hF : (edgeGraph F).IsAcyclic) :
    ∃ b : Basis n, (∀ e ∈ F, b e.val.1 ≠ b e.val.2) ∧
      squaredNorm (ket b) = 1 ∧ (∑ e ∈ F, (w e : ℝ)) ≤ energy w (ket b) := by
  classical
  obtain ⟨b, hb⟩ := forest_has_cut F hF
  refine ⟨b, hb, squaredNorm_ket b, ?_⟩
  rw [energy_ket]
  unfold cutWeight
  calc
    (∑ e ∈ F, (w e : ℝ)) =
        ∑ e ∈ F, if b e.val.1 = b e.val.2 then 0 else (w e : ℝ) := by
      apply Finset.sum_congr rfl
      intro e he
      simp only [if_neg (hb e he)]
    _ ≤ ∑ e, if b e.val.1 = b e.val.2 then 0 else (w e : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro e _ _
      split_ifs <;> positivity

/-- The computational-basis feasibility assertion of published Eq. (26). -/
theorem published_forest_energy_lower {n : ℕ} (F : Finset (Edge n)) (w : Weights n)
    (hF : (⨆ e ∈ F, SimpleGraph.edge e.val.1 e.val.2).IsAcyclic) :
    ∃ b : Basis n, (∀ e ∈ F, b e.val.1 ≠ b e.val.2) ∧
      squaredNorm (fun x => if x = b then 1 else 0) = 1 ∧
      (∑ e ∈ F, (w e : ℝ)) ≤ energy w (fun x => if x = b then 1 else 0) := by
  exact forest_energy_lower F w hF


end QuantumMaxCutEnergy.PublishedAGM



-- Proof source: baseline/next-half/MatchingLowerWave.lean


noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.Star

def pairAmplitude {n : ℕ} (e : Edge n) (x : Basis n) : ℂ :=
  if x e.val.1 = x e.val.2 then 0 else if x e.val.1 then -1 else 1

def matchingWave {n : ℕ} (m : Finset (Edge n)) : Wave n :=
  fun x => ∏ e ∈ m, pairAmplitude e x

lemma pairAmplitude_swap_self {n : ℕ} (e : Edge n) (x : Basis n) :
    pairAmplitude e (x ∘ Equiv.swap e.val.1 e.val.2) = -pairAmplitude e x := by
  simp only [pairAmplitude, Function.comp_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  cases h1 : x e.val.1 <;> cases h2 : x e.val.2 <;> norm_num

lemma pairAmplitude_swap_disjoint {n : ℕ} (e f : Edge n)
    (h : Disjoint (endpoints e) (endpoints f)) (x : Basis n) :
    pairAmplitude f (x ∘ Equiv.swap e.val.1 e.val.2) = pairAmplitude f x := by
  have hi1 : f.val.1 ≠ e.val.1 := by
    intro he
    exact Finset.disjoint_left.mp h
      (show f.val.1 ∈ endpoints e by simp [endpoints, ← he])
      (show f.val.1 ∈ endpoints f by simp [endpoints])
  have hi2 : f.val.1 ≠ e.val.2 := by
    intro he
    exact Finset.disjoint_left.mp h
      (show f.val.1 ∈ endpoints e by simp [endpoints, ← he])
      (show f.val.1 ∈ endpoints f by simp [endpoints])
  have hj1 : f.val.2 ≠ e.val.1 := by
    intro he
    exact Finset.disjoint_left.mp h
      (show f.val.2 ∈ endpoints e by simp [endpoints, ← he])
      (show f.val.2 ∈ endpoints f by simp [endpoints])
  have hj2 : f.val.2 ≠ e.val.2 := by
    intro he
    exact Finset.disjoint_left.mp h
      (show f.val.2 ∈ endpoints e by simp [endpoints, ← he])
      (show f.val.2 ∈ endpoints f by simp [endpoints])
  simp only [pairAmplitude, Function.comp_apply,
    Equiv.swap_apply_of_ne_of_ne hi1 hi2, Equiv.swap_apply_of_ne_of_ne hj1 hj2]

lemma matchingWave_swap {n : ℕ} (m : Finset (Edge n)) (hm : IsMatching m)
    (e : Edge n) (he : e ∈ m) (x : Basis n) :
    matchingWave m (x ∘ Equiv.swap e.val.1 e.val.2) = -matchingWave m x := by
  classical
  have hrest :
      (∏ f ∈ m.erase e, pairAmplitude f (x ∘ Equiv.swap e.val.1 e.val.2)) =
        ∏ f ∈ m.erase e, pairAmplitude f x := by
    apply Finset.prod_congr rfl
    intro f hf
    exact pairAmplitude_swap_disjoint e f
      (hm e he f (Finset.mem_erase.mp hf).2 (Ne.symm (Finset.mem_erase.mp hf).1)) x
  unfold matchingWave
  rw [← Finset.insert_erase he]
  rw [Finset.prod_insert (by simp : e ∉ m.erase e),
    Finset.prod_insert (by simp : e ∉ m.erase e), hrest, pairAmplitude_swap_self]
  ring

def matchingAssignment {n : ℕ} (m : Finset (Edge n)) : Basis n :=
  fun i => decide (i ∈ m.image (fun e => e.val.2))

lemma matchingAssignment_first {n : ℕ} (m : Finset (Edge n)) (hm : IsMatching m)
    (e : Edge n) (he : e ∈ m) : matchingAssignment m e.val.1 = false := by
  classical
  have hn : e.val.1 ∉ m.image (fun f => f.val.2) := by
    rintro h
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp h
    by_cases hEq : e = f
    · subst f
      exact (ne_of_lt e.property) hfe.symm
    · exact Finset.disjoint_left.mp (hm e he f hf hEq)
        (show e.val.1 ∈ endpoints e by simp [endpoints])
        (show e.val.1 ∈ endpoints f by simp [endpoints, hfe])
  simp [matchingAssignment, hn]

lemma matchingAssignment_second {n : ℕ} (m : Finset (Edge n))
    (e : Edge n) (he : e ∈ m) : matchingAssignment m e.val.2 = true := by
  classical
  simp [matchingAssignment, Finset.mem_image_of_mem (fun e : Edge n => e.val.2) he]

lemma matchingWave_nonzero {n : ℕ} (m : Finset (Edge n)) (hm : IsMatching m) :
    matchingWave m (matchingAssignment m) = 1 := by
  classical
  apply Finset.prod_eq_one
  intro e he
  simp [pairAmplitude, matchingAssignment_first m hm e he,
    matchingAssignment_second m e he]

lemma matchingWave_norm_pos {n : ℕ} (m : Finset (Edge n)) (hm : IsMatching m) :
    0 < squaredNorm (matchingWave m) := by
  classical
  have h : (1 : ℝ) ≤ squaredNorm (matchingWave m) := by
    calc
      1 = Complex.normSq (matchingWave m (matchingAssignment m)) := by
        rw [matchingWave_nonzero m hm]
        norm_num
      _ ≤ ∑ x, Complex.normSq (matchingWave m x) :=
        Finset.single_le_sum (fun x _ => Complex.normSq_nonneg _) (Finset.mem_univ _)
  linarith

lemma squaredNorm_realScale {n : ℕ} (a : ℝ) (ψ : Wave n) :
    squaredNorm (realScale a ψ) = a ^ 2 * squaredNorm ψ := by
  rw [← realInner_self, realInner_scale_left, realInner_scale_right, realInner_self]
  ring

def matchingState {n : ℕ} (m : Finset (Edge n)) : Wave n :=
  realScale (Real.sqrt (squaredNorm (matchingWave m)))⁻¹ (matchingWave m)

lemma matchingState_norm {n : ℕ} (m : Finset (Edge n)) (hm : IsMatching m) :
    squaredNorm (matchingState m) = 1 := by
  have hn := matchingWave_norm_pos m hm
  have hs : Real.sqrt (squaredNorm (matchingWave m)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hn)
  unfold matchingState
  rw [squaredNorm_realScale, inv_pow, Real.sq_sqrt hn.le]
  exact inv_mul_cancel₀ (ne_of_gt hn)

lemma matchingState_swap {n : ℕ} (m : Finset (Edge n)) (hm : IsMatching m)
    (e : Edge n) (he : e ∈ m) (x : Basis n) :
    matchingState m (x ∘ Equiv.swap e.val.1 e.val.2) = -matchingState m x := by
  simp only [matchingState, realScale, matchingWave_swap m hm e he]
  ring

lemma pairEnergy_of_antisymmetric {n : ℕ} (a b : Fin n) (ψ : Wave n)
    (hψ : squaredNorm ψ = 1)
    (hs : ∀ x, ψ (x ∘ Equiv.swap a b) = -ψ x) : pairEnergy a b ψ = 2 := by
  have he : edgeAction a b ψ = realScale 2 ψ := by
    funext x
    simp only [edgeAction, swapWave, Pi.sub_apply, realScale, hs]
    push_cast
    ring
  rw [pairEnergy, he, realInner_scale_right, realInner_self, hψ]
  norm_num

theorem matching_energy_lower {n : ℕ} (w : Weights n) (m : Finset (Edge n))
    (hm : IsMatching m) :
    2 * (∑ e ∈ m, (w e : ℝ)) ≤ optimum ⟨n, w⟩ := by
  classical
  have hp (e : Edge n) (he : e ∈ m) :
      pairEnergy e.val.1 e.val.2 (matchingState m) = 2 :=
    pairEnergy_of_antisymmetric _ _ _ (matchingState_norm m hm)
      (matchingState_swap m hm e he)
  have he : 2 * (∑ e ∈ m, (w e : ℝ)) ≤ energy w (matchingState m) := by
    rw [energy_eq_pairEnergy]
    calc
      _ = ∑ e ∈ m, (w e : ℝ) * pairEnergy e.val.1 e.val.2 (matchingState m) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        rw [hp e he]
        ring
      _ ≤ ∑ e, (w e : ℝ) * pairEnergy e.val.1 e.val.2 (matchingState m) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun e _ _ => mul_nonneg (by positivity) (pairEnergy_nonneg _ _ _))
  exact he.trans (energy_le_optimum ⟨n, w⟩ (matchingState m) (matchingState_norm m hm))


end QuantumMaxCutEnergy.Star



-- Proof source: baseline/next-half/MatchingLowerStrong.lean


noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.Star

lemma edgeAction_of_antisymmetric {n : ℕ} (a b : Fin n) (ψ : Wave n)
    (hs : ∀ x, ψ (x ∘ Equiv.swap a b) = -ψ x) :
    edgeAction a b ψ = realScale 2 ψ := by
  funext x
  simp only [edgeAction, swapWave, Pi.sub_apply, realScale, hs]
  push_cast
  ring

/-- A qubit in an antisymmetric pair has exactly one-half QMC interaction
with every third qubit. The proof uses only the shared-center identity. -/
lemma cross_pairEnergy_of_antisymmetric {n : ℕ} (a c b : Fin n)
    (hac : a ≠ c) (hab : a ≠ b) (hcb : c ≠ b) (ψ : Wave n)
    (hψ : squaredNorm ψ = 1)
    (hs : ∀ x, ψ (x ∘ Equiv.swap a c) = -ψ x) :
    pairEnergy a b ψ = 1 / 2 := by
  have hsr : ∀ x, ψ (x ∘ Equiv.swap c a) = -ψ x := by
    intro x
    simpa only [Equiv.swap_comm c a] using hs x
  have ha := edgeAction_of_antisymmetric a c ψ hs
  have hc := edgeAction_of_antisymmetric c a ψ hsr
  have hpa := pairEnergy_of_antisymmetric a c ψ hψ hs
  have hpc := pairEnergy_of_antisymmetric c a ψ hψ hsr
  have h1 := shared_center_inner ψ a c b hac hab hcb
  have h2 := shared_center_inner ψ c a b hac.symm hcb hab
  rw [ha, realInner_scale_left] at h1
  rw [hc, realInner_scale_left] at h2
  change 2 * (2 * pairEnergy a b ψ) =
    pairEnergy a c ψ + pairEnergy a b ψ - pairEnergy c b ψ at h1
  change 2 * (2 * pairEnergy c b ψ) =
    pairEnergy c a ψ + pairEnergy c b ψ - pairEnergy a b ψ at h2
  rw [hpa] at h1
  rw [hpc] at h2
  linarith

lemma edge_eq_of_coordinates {n : ℕ} (e f : Edge n)
    (h1 : e.val.1 = f.val.1) (h2 : e.val.2 = f.val.2) : e = f := by
  apply Subtype.ext
  exact Prod.ext h1 h2

lemma cross_pairEnergy_of_touching {n : ℕ} (e f : Edge n) (hne : e ≠ f)
    (htouch : ¬Disjoint (endpoints e) (endpoints f))
    (ψ : Wave n) (hψ : squaredNorm ψ = 1)
    (hs : ∀ x, ψ (x ∘ Equiv.swap e.val.1 e.val.2) = -ψ x) :
    pairEnergy f.val.1 f.val.2 ψ = 1 / 2 := by
  have hsr : ∀ x, ψ (x ∘ Equiv.swap e.val.2 e.val.1) = -ψ x := by
    intro x
    simpa only [Equiv.swap_comm e.val.2 e.val.1] using hs x
  have hen := ne_of_lt e.property
  have hfn := ne_of_lt f.property
  by_cases h11 : f.val.1 = e.val.1
  · have h22 : e.val.2 ≠ f.val.2 := by
      intro h
      exact hne (edge_eq_of_coordinates e f h11.symm h)
    simpa only [h11] using cross_pairEnergy_of_antisymmetric
      e.val.1 e.val.2 f.val.2 hen (by simpa only [h11] using hfn) h22 ψ hψ hs
  by_cases h12 : f.val.1 = e.val.2
  · have h21 : e.val.1 ≠ f.val.2 :=
      ne_of_lt (e.property.trans (by simpa only [h12] using f.property))
    simpa only [h12] using cross_pairEnergy_of_antisymmetric
      e.val.2 e.val.1 f.val.2 hen.symm (by simpa only [h12] using hfn) h21 ψ hψ hsr
  by_cases h21 : f.val.2 = e.val.1
  · have h12 : e.val.2 ≠ f.val.1 := by
      exact (ne_of_lt ((by simpa only [h21] using f.property : f.val.1 < e.val.1).trans
        e.property)).symm
    rw [pairEnergy_comm]
    simpa only [h21] using cross_pairEnergy_of_antisymmetric
      e.val.1 e.val.2 f.val.1 hen (by simpa only [h21] using hfn.symm) h12 ψ hψ hs
  have h22 : f.val.2 = e.val.2 := by
    obtain ⟨v, hve, hvf⟩ := Finset.not_disjoint_iff.mp htouch
    simp only [endpoints, Finset.mem_insert, Finset.mem_singleton] at hve hvf
    rcases hve with hve | hve <;> rcases hvf with hvf | hvf
    · exact False.elim (h11 (hvf.symm.trans hve))
    · exact False.elim (h21 (hvf.symm.trans hve))
    · exact False.elim (h12 (hvf.symm.trans hve))
    · exact hvf.symm.trans hve
  have h1 : e.val.1 ≠ f.val.1 := by
    intro h
    exact hne (edge_eq_of_coordinates e f h h22.symm)
  rw [pairEnergy_comm]
  simpa only [h22] using cross_pairEnergy_of_antisymmetric
    e.val.2 e.val.1 f.val.1 hen.symm (by simpa only [h22] using hfn.symm) h1 ψ hψ hsr

lemma matchingState_pair_of_touching {n : ℕ} (m : Finset (Edge n))
    (hm : IsMatching m) (f : Edge n) (hf : f ∉ m)
    (htouch : ∃ e ∈ m, ¬Disjoint (endpoints e) (endpoints f)) :
    pairEnergy f.val.1 f.val.2 (matchingState m) = 1 / 2 := by
  obtain ⟨e, he, hef⟩ := htouch
  have hne : e ≠ f := by
    intro h
    exact hf (h ▸ he)
  exact cross_pairEnergy_of_touching e f hne hef _ (matchingState_norm m hm)
    (matchingState_swap m hm e he)


end QuantumMaxCutEnergy.Star



-- Proof source: baseline/next-half/MatchingExtension.lean


noncomputable section
namespace QuantumMaxCutEnergy.Star

lemma IsMatching.insert_disjoint {n : ℕ} {M : Finset (Edge n)} (hM : IsMatching M)
    (f : Edge n) (hd : ∀ e ∈ M, Disjoint (endpoints e) (endpoints f)) :
    IsMatching (insert f M) := by
  intro a ha b hb hab
  rcases Finset.mem_insert.mp ha with haf | ham
  · subst a
    rcases Finset.mem_insert.mp hb with hbf | hbm
    · exact False.elim (hab hbf.symm)
    · exact (hd b hbm).symm
  · rcases Finset.mem_insert.mp hb with hbf | hbm
    · subst b
      exact hd a ham
    · exact hM a ham b hbm hab

/-- Every matching extends to a maximal matching of the complete vertex set.
No added edge needs positive graph weight. -/
theorem exists_maximal_matching_extension {n : ℕ} (m : Finset (Edge n))
    (hm : IsMatching m) :
    ∃ M : Finset (Edge n), m ⊆ M ∧ IsMatching M ∧
      ∀ f : Edge n, f ∉ M →
        ∃ e ∈ M, ¬Disjoint (endpoints e) (endpoints f) := by
  classical
  let C := (Finset.univ : Finset (Edge n)).powerset.filter
    (fun M => m ⊆ M ∧ IsMatching M)
  have hmC : m ∈ C := by simp [C, hm]
  obtain ⟨M, hMC, hmax⟩ := C.exists_max_image Finset.card ⟨m, hmC⟩
  have hM := (Finset.mem_filter.mp hMC).2
  refine ⟨M, hM.1, hM.2, ?_⟩
  intro f hf
  by_contra h
  push Not at h
  have hmatch := hM.2.insert_disjoint f h
  have hsub : m ⊆ insert f M := hM.1.trans (Finset.subset_insert f M)
  have hiC : insert f M ∈ C := by simp [C, hsub, hmatch]
  have hcard := hmax (insert f M) hiC
  rw [Finset.card_insert_of_notMem hf] at hcard
  omega

end QuantumMaxCutEnergy.Star



-- Proof source: baseline/next-half/MatchingLowerBound.lean


noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.Star

lemma matchingState_energy {n : ℕ} (w : Weights n) (m : Finset (Edge n))
    (hm : IsMatching m)
    (hcover : ∀ f : Edge n, f ∉ m → ∃ e ∈ m, ¬Disjoint (endpoints e) (endpoints f)) :
    energy w (matchingState m) =
      (totalWeight w + 3 * (∑ e ∈ m, (w e : ℝ))) / 2 := by
  classical
  have hpair (e : Edge n) :
      pairEnergy e.val.1 e.val.2 (matchingState m) = if e ∈ m then 2 else 1 / 2 := by
    by_cases he : e ∈ m
    · rw [if_pos he]
      exact pairEnergy_of_antisymmetric _ _ _ (matchingState_norm m hm)
        (matchingState_swap m hm e he)
    · rw [if_neg he]
      exact matchingState_pair_of_touching m hm e he (hcover e he)
  rw [energy_eq_pairEnergy]
  simp_rw [hpair]
  have hsum : (∑ e : Edge n, if e ∈ m then (w e : ℝ) else 0) =
      ∑ e ∈ m, (w e : ℝ) := by
    simp
  calc
    (∑ e : Edge n, (w e : ℝ) * if e ∈ m then 2 else 1 / 2) =
        ∑ e : Edge n, ((w e : ℝ) / 2 +
          3 / 2 * (if e ∈ m then (w e : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro e he
      split_ifs <;> ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, hsum]
      unfold totalWeight
      ring

/-- The matching lower estimate is a numerical bound on the unrestricted
optimum. The auxiliary normalized vector is only an analytic witness. -/
theorem matching_energy_strong_lower {n : ℕ} (w : Weights n) (m : Finset (Edge n))
    (hm : IsMatching m) :
    (totalWeight w + 3 * (∑ e ∈ m, (w e : ℝ))) / 2 ≤ optimum ⟨n, w⟩ := by
  classical
  obtain ⟨M, hsub, hM, hcover⟩ := exists_maximal_matching_extension m hm
  have hvalue := energy_le_optimum ⟨n, w⟩ (matchingState M) (matchingState_norm M hM)
  rw [matchingState_energy w M hM hcover] at hvalue
  have hsum : (∑ e ∈ m, (w e : ℝ)) ≤ ∑ e ∈ M, (w e : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => by positivity)
  linarith


end QuantumMaxCutEnergy.Star



-- Proof source: solver-2026-11-01/runtime/IncidentFloorBridge.lean


noncomputable section
open scoped BigOperators

namespace QMCNumericRuntime.IncidentRuntime
open QuantumMaxCutEnergy QuantumMaxCutEnergy.Star
open QuantumMaxCutEnergy.PublishedAGM
open QuantumMaxCutEnergy.PublishedAGM.Incident

def priority (e : NumericEdge) : ℚ ×ₗ (ℕ ×ₗ ℕ) :=
  toLex (e.2, toLex e.1)

lemma priority_le_iff (a b : NumericEdge) :
    priority a ≤ priority b ↔ a.2 < b.2 ∨ a.2 = b.2 ∧
      (a.1.1 < b.1.1 ∨ a.1.1 = b.1.1 ∧ a.1.2 ≤ b.1.2) := by
  simp [priority, Prod.Lex.toLex_le_toLex]

lemma priority_pick (a b : NumericEdge) :
    priority (pick a b) = max (priority a) (priority b) := by
  unfold pick
  split_ifs with h1 h2 h3 h4 h5
  · exact (max_eq_right ((priority_le_iff a b).2 (Or.inl h1))).symm
  · exact (max_eq_left ((priority_le_iff b a).2 (Or.inl h2))).symm
  · have hw : a.2 = b.2 := le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
    exact (max_eq_right ((priority_le_iff a b).2 (Or.inr ⟨hw, Or.inl h3⟩))).symm
  · have hw : a.2 = b.2 := le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
    exact (max_eq_left ((priority_le_iff b a).2 (Or.inr ⟨hw.symm, Or.inl h4⟩))).symm
  · have hw : a.2 = b.2 := le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
    have hi : a.1.1 = b.1.1 := le_antisymm (le_of_not_gt h4) (le_of_not_gt h3)
    exact (max_eq_right ((priority_le_iff a b).2
      (Or.inr ⟨hw, Or.inr ⟨hi, h5.le⟩⟩))).symm
  · have hw : a.2 = b.2 := le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
    have hi : a.1.1 = b.1.1 := le_antisymm (le_of_not_gt h4) (le_of_not_gt h3)
    exact (max_eq_left ((priority_le_iff b a).2
      (Or.inr ⟨hw.symm, Or.inr ⟨hi.symm, le_of_not_gt h5⟩⟩))).symm

lemma fold_pick_max (xs : List NumericEdge) (a : NumericEdge) :
    priority a ≤ priority (xs.foldl pick a) ∧
      ∀ e ∈ xs, priority e ≤ priority (xs.foldl pick a) := by
  induction xs generalizing a with
  | nil => simp
  | cons b xs ih =>
      have h := ih (pick a b)
      constructor
      · have hh : priority a ≤ priority (pick a b) := by
          rw [priority_pick]
          exact le_max_left _ _
        exact hh.trans h.1
      · intro e he
        rcases List.mem_cons.mp he with he | hm
        · rw [he]
          have hh : priority b ≤ priority (pick a b) := by
            rw [priority_pick]
            exact le_max_right _ _
          exact hh.trans h.1
        · exact h.2 e hm

theorem best_max (xs : List NumericEdge) (e : NumericEdge) (he : e ∈ xs) :
    priority e ≤ priority (best xs) := by
  cases xs with
  | nil => simp at he
  | cons a xs =>
      simp only [best, List.tail_cons, List.head?_cons, Option.getD_some]
      rcases List.mem_cons.mp he with he | hm
      · rw [he]
        exact (fold_pick_max xs a).1
      · exact (fold_pick_max xs a).2 e hm

lemma priority_numeric_le_iff (G : Input) (e f : Edge G.n) :
    priority (numericEdge G e) ≤ priority (numericEdge G f) ↔
      weightPriority G.weights e ≤ weightPriority G.weights f := by
  simp [priority, numericEdge, weightPriority, Prod.Lex.toLex_le_toLex,
    NNRat.coe_lt_coe, NNRat.coe_inj]

lemma incident_numeric_iff (G : Input) (v : Fin G.n) (e : Edge G.n) :
    incident v.val (numericEdge G e) = true ↔ v ∈ endpoints e := by
  simp only [incident, numericEdge, Bool.or_eq_true, endpoints,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact Or.inl (Fin.ext (of_decide_eq_true h))
    · exact Or.inr (Fin.ext (of_decide_eq_true h))
  · rintro (rfl | rfl) <;> simp

lemma sameEdge_numeric_iff (G : Input) (e f : Edge G.n) :
    sameEdge (numericEdge G e) (numericEdge G f) = true ↔ e = f := by
  simp only [sameEdge, numericEdge, Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    exact Subtype.ext (Prod.ext (Fin.ext (of_decide_eq_true h1))
      (Fin.ext (of_decide_eq_true h2)))
  · rintro rfl
    simp

def selector (G : Input) : Fin G.n → Option (Edge G.n) :=
  rankIncident Finset.univ (weightPriority G.weights)

lemma incidentBest_matches_selector (G : Input) (v : Fin G.n) (e : Edge G.n)
    (hv : v ∈ endpoints e) :
    ∃ f, selector G v = some f ∧
      incidentBest (inputEdges G, v.val) = numericEdge G f := by
  classical
  have heraw : numericEdge G e ∈ (inputEdges G).filter (incident v.val) := by
    exact List.mem_filter.mpr ⟨(mem_inputEdges G _).2 ⟨e, rfl⟩,
      (incident_numeric_iff G v e).2 hv⟩
  have hne : (inputEdges G).filter (incident v.val) ≠ [] := by
    intro h
    simpa only [h, List.not_mem_nil] using heraw
  have hbest := best_mem ((inputEdges G).filter (incident v.val)) hne
  obtain ⟨g, hg⟩ := (mem_inputEdges G _).1 (List.mem_filter.mp hbest).1
  have hgv : v ∈ endpoints g := (incident_numeric_iff G v g).1 (by
    simpa only [hg] using (List.mem_filter.mp hbest).2)
  have hn : (incidentEdges (Finset.univ : Finset (Edge G.n)) v).Nonempty :=
    ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
  obtain ⟨f, hf⟩ : ∃ f, selector G v = some f := by
    unfold selector rankIncident
    exact ⟨_, dif_pos hn⟩
  have hfv : v ∈ endpoints f := (rankIncident_valid Finset.univ
    (weightPriority G.weights) v f hf).2
  have hle : weightPriority G.weights f ≤ weightPriority G.weights g := by
    apply (priority_numeric_le_iff G f g).1
    rw [hg]
    exact best_max _ _ (List.mem_filter.mpr
      ⟨(mem_inputEdges G _).2 ⟨f, rfl⟩, (incident_numeric_iff G v f).2 hfv⟩)
  have hge : weightPriority G.weights g ≤ weightPriority G.weights f :=
    rankIncident_max Finset.univ (weightPriority G.weights) v f hf g
      (Finset.mem_univ _) hgv
  have hfg : f = g := weightPriority_injective G.weights (le_antisymm hle hge)
  refine ⟨f, hf, ?_⟩
  change best ((inputEdges G).filter (incident v.val)) = numericEdge G f
  rw [hfg]
  exact hg.symm

lemma endpoint_selected_iff (G : Input) (e : Edge G.n) (v : Fin G.n)
    (hv : v ∈ endpoints e) :
    sameEdge (incidentBest (inputEdges G, v.val)) (numericEdge G e) = true ↔
      selector G v = some e := by
  obtain ⟨f, hf, hb⟩ := incidentBest_matches_selector G v e hv
  rw [hb, sameEdge_numeric_iff, hf, Option.some.injEq]

lemma selectedTest_numeric_iff (G : Input) (e : Edge G.n) :
    selectedTest (inputEdges G, numericEdge G e) = true ↔
      e ∈ selectedEdges Finset.univ (selector G) := by
  classical
  change (sameEdge (incidentBest (inputEdges G, e.val.1.val)) (numericEdge G e) ||
    sameEdge (incidentBest (inputEdges G, e.val.2.val)) (numericEdge G e)) = true ↔ _
  rw [Bool.or_eq_true]
  rw [endpoint_selected_iff G e e.val.1 (by simp [endpoints]),
    endpoint_selected_iff G e e.val.2 (by simp [endpoints])]
  simp only [selectedEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (selected_iff_endpoints Finset.univ (selector G)
    (rankIncident_valid Finset.univ (weightPriority G.weights)) e).symm

lemma mutualTest_numeric_iff (G : Input) (e : Edge G.n) :
    mutualTest (inputEdges G, numericEdge G e) = true ↔
      e ∈ QuantumMaxCutEnergy.PublishedAGM.Incident.mutualEdges Finset.univ (selector G) := by
  classical
  change (sameEdge (incidentBest (inputEdges G, e.val.1.val)) (numericEdge G e) &&
    sameEdge (incidentBest (inputEdges G, e.val.2.val)) (numericEdge G e)) = true ↔ _
  rw [Bool.and_eq_true]
  rw [endpoint_selected_iff G e e.val.1 (by simp [endpoints]),
    endpoint_selected_iff G e e.val.2 (by simp [endpoints])]
  simp [QuantumMaxCutEnergy.PublishedAGM.Incident.mutualEdges]

end QMCNumericRuntime.IncidentRuntime



-- Proof source: solver-2026-11-01/runtime/IncidentFloorBounds.lean


noncomputable section
open scoped BigOperators

namespace QMCNumericRuntime.IncidentRuntime
open QuantumMaxCutEnergy QuantumMaxCutEnergy.Star
open QuantumMaxCutEnergy.PublishedAGM
open QuantumMaxCutEnergy.PublishedAGM.Incident

def typedMatching (G : Input) : Finset (Edge G.n) :=
  Incident.mutualEdges Finset.univ (selector G)

def typedForest (G : Input) : Finset (Edge G.n) :=
  selectedEdges Finset.univ (selector G)

lemma sum_filter_map {α : Type} (xs : List α) (p : α → Bool) (f : α → ℚ) :
    ((xs.filter p).map f).sum = (xs.map (fun x => if p x then f x else 0)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases hp : p x <;> simp [hp, ih]

lemma filtered_input_sum (G : Input) (p : NumericEdge → Bool) :
    edgeWeightSum ((inputEdges G).filter p) =
      ∑ e : Edge G.n, if p (numericEdge G e) then (G.weights e : ℚ) else 0 := by
  let G' : Input := ⟨G.n, fun e => if p (numericEdge G e) then G.weights e else 0⟩
  have hmap : (inputEdges G').map Prod.snd =
      (inputEdges G).map (fun e => if p e then e.2 else 0) := by
    simp only [inputEdges, List.map_map]
    congr 1
    funext e
    change ((if p (numericEdge G e) then G.weights e else 0 : ℚ≥0) : ℚ) =
      if p (numericEdge G e) then (G.weights e : ℚ) else 0
    split_ifs <;> rfl
  have h := inputEdges_weight_sum G'
  rw [edgeWeightSum, hmap] at h
  rw [edgeWeightSum, sum_filter_map]
  simpa only [G', apply_ite, NNRat.coe_zero] using h

lemma filtered_input_sum_real (G : Input) (p : NumericEdge → Bool) :
    ((edgeWeightSum ((inputEdges G).filter p) : ℚ) : ℝ) =
      ∑ e : Edge G.n, if p (numericEdge G e) then (G.weights e : ℝ) else 0 := by
  rw [filtered_input_sum, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro e he
  split_ifs <;> simp

lemma forestWeight_real (G : Input) :
    ((forestWeight (inputEdges G) : ℚ) : ℝ) =
      ∑ e ∈ typedForest G, (G.weights e : ℝ) := by
  rw [forestWeight, selected, filtered_input_sum_real]
  calc
    _ = ∑ e : Edge G.n, if e ∈ typedForest G then (G.weights e : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      have hh := selectedTest_numeric_iff G e
      change (selectedTest (inputEdges G, numericEdge G e) = true ↔ e ∈ typedForest G) at hh
      simp only [hh]
    _ = _ := by simp

lemma matchingWeight_real (G : Input) :
    ((matchingWeight (inputEdges G) : ℚ) : ℝ) =
      ∑ e ∈ typedMatching G, (G.weights e : ℝ) := by
  rw [matchingWeight, mutualEdges, filtered_input_sum_real]
  calc
    _ = ∑ e : Edge G.n, if e ∈ typedMatching G then (G.weights e : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      have hh := mutualTest_numeric_iff G e
      change (mutualTest (inputEdges G, numericEdge G e) = true ↔ e ∈ typedMatching G) at hh
      simp only [hh]
    _ = _ := by simp

lemma inputWeight_real (G : Input) :
    ((edgeWeightSum (inputEdges G) : ℚ) : ℝ) = totalWeight G.weights := by
  rw [inputEdges_weight_sum, Rat.cast_sum]
  simp [totalWeight]

lemma floorValue_cast (G : Input) :
    (floorValue G : ℝ) = max (∑ e ∈ typedForest G, (G.weights e : ℝ))
      ((totalWeight G.weights + 3 * ∑ e ∈ typedMatching G, (G.weights e : ℝ)) / 2) := by
  change ((rawFloor (inputEdges G) : ℚ) : ℝ) = _
  simp only [rawFloor, Rat.cast_max, Rat.cast_div, Rat.cast_add, Rat.cast_mul,
    Rat.cast_ofNat, forestWeight_real, matchingWeight_real, inputWeight_real]

lemma matching_isMatching (G : Input) : IsMatching (typedMatching G) :=
  Incident.mutual_isMatching Finset.univ (selector G)

lemma forest_isAcyclic (G : Input) : (edgeGraph (typedForest G)).IsAcyclic :=
  selectedEdges_isAcyclic Finset.univ (selector G)
    (rankIncident_valid Finset.univ (weightPriority G.weights))
    (weightPriority G.weights) (weightPriority_injective G.weights)
    (rankIncident_max Finset.univ (weightPriority G.weights))

lemma matching_subset_forest (G : Input) : typedMatching G ⊆ typedForest G :=
  mutual_subset_selected Finset.univ (selector G)

lemma forest_optimum_lower (G : Input) :
    (∑ e ∈ typedForest G, (G.weights e : ℝ)) ≤ optimum G := by
  obtain ⟨b, _, hn, he⟩ := forest_energy_lower (typedForest G) G.weights (forest_isAcyclic G)
  exact he.trans (energy_le_optimum G _ hn)

lemma floorValue_sound (G : Input) : (floorValue G : ℝ) ≤ optimum G := by
  rw [floorValue_cast]
  exact max_le (forest_optimum_lower G)
    (matching_energy_strong_lower G.weights (typedMatching G) (matching_isMatching G))

def halfEdge (G : Input) (c i : Fin G.n) : ℝ :=
  if h : c < i then (G.weights ⟨(c, i), h⟩ : ℝ) / 2
  else if h : i < c then (G.weights ⟨(i, c), h⟩ : ℝ) / 2 else 0

lemma halfEdge_le_incident_maximum (G : Input) (c i : Fin G.n) :
    halfEdge G c i ≤ (incidentMaximum Finset.univ G.weights c : ℝ) / 2 := by
  unfold halfEdge
  split_ifs with h1 h2
  · have hh : G.weights ⟨(c, i), h1⟩ ≤ incidentMaximum Finset.univ G.weights c := by
      apply Finset.le_sup
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [endpoints]⟩
    have hh' : (G.weights ⟨(c, i), h1⟩ : ℝ) ≤
        (incidentMaximum Finset.univ G.weights c : ℝ) := by exact_mod_cast hh
    exact div_le_div_of_nonneg_right hh' (by norm_num)
  · have hh : G.weights ⟨(i, c), h2⟩ ≤ incidentMaximum Finset.univ G.weights c := by
      apply Finset.le_sup
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [endpoints]⟩
    have hh' : (G.weights ⟨(i, c), h2⟩ : ℝ) ≤
        (incidentMaximum Finset.univ G.weights c : ℝ) := by exact_mod_cast hh
    exact div_le_div_of_nonneg_right hh' (by norm_num)
  · positivity

lemma incident_optimum_upper (G : Input) :
    optimum G ≤ totalWeight G.weights +
      (∑ v, (incidentMaximum Finset.univ G.weights v : ℝ)) / 2 := by
  have hdiag : ∀ i, halfEdge G i i = 0 := by intro i; simp [halfEdge]
  have hparts : ∀ e : Edge G.n,
      halfEdge G e.val.1 e.val.2 + halfEdge G e.val.2 e.val.1 = (G.weights e : ℝ) := by
    intro e
    simp only [halfEdge, dif_pos e.property,
      dif_neg (not_lt_of_ge e.property.le)]
    ring
  have hv : ∀ c i, 0 ≤ halfEdge G c i := by
    intro c i
    unfold halfEdge
    split_ifs <;> positivity
  have hh := optimum_le_star_cover G.weights (halfEdge G)
    (fun v => (incidentMaximum Finset.univ G.weights v : ℝ) / 2)
    hdiag hparts hv (fun _ => by positivity)
    (fun c i _ => halfEdge_le_incident_maximum G c i)
  rwa [← Finset.sum_div] at hh

lemma incident_weight_sum (G : Input) :
    (∑ v, (incidentMaximum Finset.univ G.weights v : ℝ)) =
      (∑ e ∈ typedMatching G, (G.weights e : ℝ)) +
        ∑ e ∈ typedForest G, (G.weights e : ℝ) := by
  have hh := incident_weight_identity Finset.univ G.weights (selector G)
    (rankIncident_valid Finset.univ (weightPriority G.weights))
  simpa only [selector, rankIncident_weight_eq_max, typedMatching, typedForest] using hh

theorem floorValue_agm_bounds (G : Input) :
    (floorValue G : ℝ) ≤ optimum G ∧ ∃ m f : ℝ,
      0 ≤ m ∧ m ≤ f ∧ f ≤ (∑ e, (G.weights e : ℝ)) ∧
      optimum G ≤ (∑ e, (G.weights e : ℝ)) + (m + f) / 2 ∧
      f ≤ (floorValue G : ℝ) ∧
      ((∑ e, (G.weights e : ℝ)) + 3 * m) / 2 ≤ (floorValue G : ℝ) := by
  classical
  refine ⟨floorValue_sound G,
    ∑ e ∈ typedMatching G, (G.weights e : ℝ),
    ∑ e ∈ typedForest G, (G.weights e : ℝ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · exact Finset.sum_le_sum_of_subset_of_nonneg (matching_subset_forest G)
      (fun _ _ _ => by positivity)
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => by positivity)
  · have hh := incident_optimum_upper G
    rwa [incident_weight_sum] at hh
  · rw [floorValue_cast]
    exact le_max_left _ _
  · rw [floorValue_cast]
    exact le_max_right _ _

end QMCNumericRuntime.IncidentRuntime

theorem solution :
    ∃ b : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime
        QuantumMaxCutEnergy.encodeRequest QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => b request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input,
        (b G : ℝ) ≤ QuantumMaxCutEnergy.optimum G ∧
        ∃ m f : ℝ,
          0 ≤ m ∧ m ≤ f ∧ f ≤ (∑ e, (G.weights e : ℝ)) ∧
          QuantumMaxCutEnergy.optimum G ≤ (∑ e, (G.weights e : ℝ)) + (m + f) / 2 ∧
          f ≤ (b G : ℝ) ∧
          ((∑ e, (G.weights e : ℝ)) + 3 * m) / 2 ≤ (b G : ℝ) := by
  exact ⟨QMCNumericRuntime.IncidentRuntime.floorValue,
    QMCNumericRuntime.IncidentRuntime.floor_polynomialTime,
    QMCNumericRuntime.IncidentRuntime.floorValue_agm_bounds⟩




#print axioms solution
