-- Prove2me | solution 1 for QuantumMaxCutEnergy.uniform_star_saturation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T00:56:59.738708+00:00
-- url     : https://prove2.me/submissions/37b5b530-758f-4d28-8c5c-d68d40f3d4fa

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel

-- Local source: baseline/next-half/Antisymmetrizer.lean

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

end

-- Local source: baseline/next-half/RealInner.lean

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

end

-- Local source: baseline/next-half/WeightedStar.lean

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

end

-- Local source: baseline/AnalyticProof.lean

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


end

-- Local source: published-agm/UniformStar.lean

/-!
Published source: Anshu, Gosset, Morenz, TQC 2020,
doi:10.4230/LIPIcs.TQC.2020.7, p. 7:7, remark after Eq. (12).
The weighted-star upper bound is attained for a nonempty uniform star.
This proof constructs the one-excitation Laplacian eigenvector explicitly.
-/

noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.PublishedAGM
open QuantumMaxCutEnergy.Star
open QuantumMaxCutEnergy.BaselineSemantic

def oneHot {n : ℕ} (k : Fin n) : Basis n := fun j => decide (j = k)

lemma oneHot_injective {n : ℕ} : Function.Injective (@oneHot n) := by
  intro i j h
  have hh := congrFun h i
  simpa [oneHot] using hh

lemma oneHot_swap {n : ℕ} (a b k : Fin n) :
    oneHot k ∘ Equiv.swap a b = oneHot (Equiv.swap a b k) := by
  funext j
  simp only [oneHot, Function.comp_apply, Equiv.swap_apply_eq_iff]

def oneParticle {n : ℕ} (v : Fin n → ℂ) : Wave n :=
  fun x => ∑ k, v k * ket (oneHot k) x

lemma oneParticle_at_oneHot {n : ℕ} (v : Fin n → ℂ) (k : Fin n) :
    oneParticle v (oneHot k) = v k := by
  classical
  have h (j : Fin n) : (oneHot k = oneHot j) ↔ k = j := oneHot_injective.eq_iff
  simp [oneParticle, ket, h]

lemma oneParticle_swap {n : ℕ} (v : Fin n → ℂ) (a b : Fin n) :
    swapWave a b (oneParticle v) = oneParticle (fun k => v (Equiv.swap a b k)) := by
  funext x
  simp only [swapWave, oneParticle, ket_swap, oneHot_swap]
  have h := Equiv.sum_comp (Equiv.swap a b)
    (fun k => v k * ket (oneHot (Equiv.swap a b k)) x)
  simpa only [Equiv.swap_apply_self] using h.symm

lemma oneParticle_sub {n : ℕ} (u v : Fin n → ℂ) :
    oneParticle (u - v) = oneParticle u - oneParticle v := by
  funext x
  simp [oneParticle, sub_mul, Finset.sum_sub_distrib]

lemma oneParticle_sum {n : ℕ} {ι : Type*} (s : Finset ι) (v : ι → Fin n → ℂ) :
    oneParticle (∑ i ∈ s, v i) = ∑ i ∈ s, oneParticle (v i) := by
  classical
  funext x
  simp only [oneParticle, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

lemma oneParticle_scale {n : ℕ} (t : ℝ) (v : Fin n → ℂ) :
    oneParticle (fun k => (t : ℂ) * v k) = realScale t (oneParticle v) := by
  funext x
  simp only [oneParticle, realScale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma uniformStarAction_oneParticle {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (v : Fin n → ℂ) :
    starAction c s (fun _ => 1) (oneParticle v) =
      oneParticle (fun k => ∑ i ∈ s, (v k - v (Equiv.swap c i k))) := by
  have h (i : Fin n) : edgeAction c i (oneParticle v) =
      oneParticle (fun k => v k - v (Equiv.swap c i k)) := by
    rw [edgeAction, oneParticle_swap, ← oneParticle_sub]
    rfl
  have h1 (φ : Wave n) : realScale 1 φ = φ := by funext x; simp [realScale]
  simp only [starAction, h1, h]
  rw [← oneParticle_sum]
  congr 1
  funext k
  simp only [Finset.sum_apply]

def starCoefficients {n : ℕ} (c : Fin n) (s : Finset (Fin n)) (k : Fin n) : ℂ :=
  if k = c then (s.card : ℂ) else if k ∈ s then -1 else 0

lemma starCoefficients_center {n : ℕ} (c : Fin n) (s : Finset (Fin n)) :
    starCoefficients c s c = s.card := by simp [starCoefficients]

lemma starCoefficients_leaf {n : ℕ} (c : Fin n) (s : Finset (Fin n)) (hc : c ∉ s)
    (i : Fin n) (hi : i ∈ s) : starCoefficients c s i = -1 := by
  have hic : i ≠ c := by intro h; exact hc (h ▸ hi)
  simp [starCoefficients, hic, hi]

lemma starCoefficients_eigen {n : ℕ} (c : Fin n) (s : Finset (Fin n)) (hc : c ∉ s)
    (k : Fin n) :
    (∑ i ∈ s, (starCoefficients c s k - starCoefficients c s (Equiv.swap c i k))) =
      ((s.card : ℂ) + 1) * starCoefficients c s k := by
  classical
  by_cases hk : k = c
  · subst k
    have hsum : (∑ i ∈ s, starCoefficients c s i) = ∑ _i ∈ s, (-1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact starCoefficients_leaf c s hc i hi
    simp only [Equiv.swap_apply_left, starCoefficients_center, Finset.sum_sub_distrib]
    rw [hsum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  · by_cases hks : k ∈ s
    · rw [starCoefficients_leaf c s hc k hks]
      have hterm (i : Fin n) (hi : i ∈ s) :
          (-1 : ℂ) - starCoefficients c s (Equiv.swap c i k) =
            if i = k then -1 - (s.card : ℂ) else 0 := by
        by_cases hik : i = k
        · subst i
          simp [starCoefficients_center]
        · rw [Equiv.swap_apply_of_ne_of_ne hk (Ne.symm hik),
            starCoefficients_leaf c s hc k hks, if_neg hik]
          ring
      rw [Finset.sum_congr rfl hterm]
      simp [hks]
      ring
    · have hother : starCoefficients c s k = 0 := by simp [starCoefficients, hk, hks]
      rw [hother, mul_zero]
      apply Finset.sum_eq_zero
      intro i hi
      have hki : k ≠ i := by intro h; exact hks (h ▸ hi)
      rw [Equiv.swap_apply_of_ne_of_ne hk hki, hother]
      ring

def uniformStarWave {n : ℕ} (c : Fin n) (s : Finset (Fin n)) : Wave n :=
  oneParticle (starCoefficients c s)

lemma uniformStarWave_eigen {n : ℕ} (c : Fin n) (s : Finset (Fin n)) (hc : c ∉ s) :
    starAction c s (fun _ => 1) (uniformStarWave c s) =
      realScale ((s.card : ℝ) + 1) (uniformStarWave c s) := by
  rw [uniformStarWave, uniformStarAction_oneParticle, ← oneParticle_scale]
  congr 1
  funext k
  push_cast
  exact starCoefficients_eigen c s hc k

lemma uniformStarWave_nonzero {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (hs : s.Nonempty) : 0 < squaredNorm (uniformStarWave c s) := by
  have hd : 0 < s.card := Finset.card_pos.mpr hs
  have hp : uniformStarWave c s (oneHot c) = (s.card : ℂ) := by
    rw [uniformStarWave, oneParticle_at_oneHot, starCoefficients_center]
  have hn : 0 < Complex.normSq (uniformStarWave c s (oneHot c)) := by
    rw [hp]
    apply Complex.normSq_pos.mpr
    exact_mod_cast (ne_of_gt hd)
  have hle : Complex.normSq (uniformStarWave c s (oneHot c)) ≤
      squaredNorm (uniformStarWave c s) := by
    exact Finset.single_le_sum (fun x _ => Complex.normSq_nonneg _)
      (Finset.mem_univ (oneHot c))
  exact hn.trans_le hle

lemma edgeAction_scale {n : ℕ} (a b : Fin n) (t : ℝ) (ψ : Wave n) :
    edgeAction a b (realScale t ψ) = realScale t (edgeAction a b ψ) := by
  funext x
  simp only [edgeAction, realScale, swapWave, Pi.sub_apply]
  ring

lemma pairEnergy_scale {n : ℕ} (a b : Fin n) (t : ℝ) (ψ : Wave n) :
    pairEnergy a b (realScale t ψ) = t ^ 2 * pairEnergy a b ψ := by
  rw [pairEnergy, edgeAction_scale, realInner_scale_left, realInner_scale_right]
  unfold pairEnergy
  ring

lemma starEnergy_scale {n : ℕ} (c : Fin n) (s : Finset (Fin n)) (w : Fin n → ℝ)
    (t : ℝ) (ψ : Wave n) :
    starEnergy c s w (realScale t ψ) = t ^ 2 * starEnergy c s w ψ := by
  unfold starEnergy
  simp_rw [pairEnergy_scale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma squaredNorm_scale {n : ℕ} (a : ℝ) (ψ : Wave n) :
    squaredNorm (realScale a ψ) = a ^ 2 * squaredNorm ψ := by
  rw [← realInner_self, realInner_scale_left, realInner_scale_right, realInner_self]
  ring

def uniformStarState {n : ℕ} (c : Fin n) (s : Finset (Fin n)) : Wave n :=
  realScale (Real.sqrt (squaredNorm (uniformStarWave c s)))⁻¹ (uniformStarWave c s)

lemma uniformStarState_norm {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (hs : s.Nonempty) : squaredNorm (uniformStarState c s) = 1 := by
  have hn := uniformStarWave_nonzero c s hs
  unfold uniformStarState
  rw [squaredNorm_scale, inv_pow, Real.sq_sqrt hn.le]
  exact inv_mul_cancel₀ (ne_of_gt hn)

lemma uniformStarState_energy {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (hc : c ∉ s) (hs : s.Nonempty) :
    starEnergy c s (fun _ => 1) (uniformStarState c s) = (s.card : ℝ) + 1 := by
  have hn := uniformStarWave_nonzero c s hs
  have he : starEnergy c s (fun _ => 1) (uniformStarWave c s) =
      ((s.card : ℝ) + 1) * squaredNorm (uniformStarWave c s) := by
    rw [← starAction_inner, uniformStarWave_eigen c s hc,
      realInner_scale_right, realInner_self]
  unfold uniformStarState
  rw [starEnergy_scale, he, inv_pow, Real.sq_sqrt hn.le]
  field_simp

/-- The equality case explicitly recorded after Eq. (12), p. 7:7, of the
published TQC2020 paper. Extra vertices outside the star are permitted. -/
theorem uniform_star_saturation {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (hc : c ∉ s) (hs : s.Nonempty) :
    (∀ ψ : Wave n, squaredNorm ψ = 1 →
      (∑ i ∈ s, (∑ x, Complex.normSq
        (ψ x - ψ (x ∘ Equiv.swap c i))) / 2) ≤ (s.card : ℝ) + 1) ∧
    ∃ ψ : Wave n, squaredNorm ψ = 1 ∧
      (∑ i ∈ s, (∑ x, Complex.normSq
        (ψ x - ψ (x ∘ Equiv.swap c i))) / 2) = (s.card : ℝ) + 1 := by
  constructor
  · intro ψ hψ
    have h := weighted_star_energy_upper_bound c s (fun _ => 1) ψ 1 hc
      (fun _ _ => by norm_num) (by norm_num) (fun _ _ => le_rfl) hψ
    simpa only [one_div, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul, div_eq_mul_inv,
      mul_comm] using h
  · refine ⟨uniformStarState c s, uniformStarState_norm c s hs, ?_⟩
    have he := uniformStarState_energy c s hc hs
    simp only [starEnergy, one_mul, pairEnergy_eq] at he
    exact he


end QuantumMaxCutEnergy.PublishedAGM

end

theorem solution {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (hc : c ∉ s) (hs : s.Nonempty) :
    (∀ ψ : QuantumMaxCutEnergy.Wave n, QuantumMaxCutEnergy.squaredNorm ψ = 1 →
      (∑ i ∈ s, (∑ x, Complex.normSq
        (ψ x - ψ (x ∘ Equiv.swap c i))) / 2) ≤ (s.card : ℝ) + 1) ∧
    ∃ ψ : QuantumMaxCutEnergy.Wave n, QuantumMaxCutEnergy.squaredNorm ψ = 1 ∧
      (∑ i ∈ s, (∑ x, Complex.normSq
        (ψ x - ψ (x ∘ Equiv.swap c i))) / 2) = (s.card : ℝ) + 1 := by
  exact QuantumMaxCutEnergy.PublishedAGM.uniform_star_saturation c s hc hs

#print axioms solution
