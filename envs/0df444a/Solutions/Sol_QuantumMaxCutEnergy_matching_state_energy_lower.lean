-- Prove2me | solution 1 for QuantumMaxCutEnergy.matching_state_energy_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T15:18:50.398268+00:00
-- url     : https://prove2.me/submissions/60af2c67-2d05-458f-b3d5-fa4effc9ff0c

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel

/-! Singlets on a matching, extended to a maximal matching of the complete vertex set:
the resulting state has energy `(W + 3 w(M)) / 2`, a lower bound on the optimum.
Source: Anshu, Gosset, Morenz, TQC 2020, https://doi.org/10.4230/LIPIcs.TQC.2020.7, Eq. (25). -/

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




open scoped BigOperators

theorem solution {n : ℕ}
    (w : QuantumMaxCutEnergy.Weights n) (M : Finset (QuantumMaxCutEnergy.Edge n))
    (hM : ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
      e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) :
    ((∑ e, (w e : ℝ)) + 3 * ∑ e ∈ M, (w e : ℝ)) / 2 ≤
      QuantumMaxCutEnergy.optimum ⟨n, w⟩ := by
  have hm : QuantumMaxCutEnergy.Star.IsMatching M := by
    intro e he f hf hef
    obtain ⟨h1, h2, h3, h4⟩ := hM e he f hf hef
    simp only [QuantumMaxCutEnergy.Star.endpoints, Finset.disjoint_insert_left,
      Finset.mem_insert, Finset.mem_singleton, Finset.disjoint_singleton_left, not_or]
    exact ⟨⟨h1, h2⟩, h3, h4⟩
  have h := QuantumMaxCutEnergy.Star.matching_energy_strong_lower w M hm
  simpa [QuantumMaxCutEnergy.totalWeight] using h
