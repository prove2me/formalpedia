-- Prove2me | solution 1 for QuantumMaxCutEnergy.agm_sdp_structural_domination
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T14:54:28.052744+00:00
-- url     : https://prove2.me/submissions/3beb0da1-19b5-4fb0-864a-ad556c49f8e9

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

-- Local verified source: /Users/macbookpro/prove2me-shuze/Prove2me/output/quantum-maxcut-statement/energy-estimation/baseline/next-half/Antisymmetrizer.lean


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


-- Local verified source: /Users/macbookpro/prove2me-shuze/Prove2me/output/quantum-maxcut-statement/energy-estimation/baseline/next-half/RealInner.lean


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


-- Local verified source: /Users/macbookpro/prove2me-shuze/Prove2me/output/quantum-maxcut-statement/energy-estimation/baseline/next-half/WeightedStar.lean


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


-- Local verified source: /Users/macbookpro/prove2me-shuze/Prove2me/output/quantum-maxcut-statement/energy-estimation/baseline/AnalyticProof.lean


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



-- Local verified source: /Users/macbookpro/prove2me-shuze/Prove2me/output/quantum-maxcut-statement/energy-estimation/baseline/next-half/StarCover.lean


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


-- Local verified source: /Users/macbookpro/prove2me-shuze/Prove2me/output/quantum-maxcut-statement/solver-2026-11-01/agm-route/AGMPauliGram.lean


/-!
Direct semantic bridge from a QMC amplitude vector to a feasible classical
Max-Cut SDP Gram matrix. The features are X_i ψ, Y_i ψ, Z_i ψ. This avoids
constructing product states or global measurement-basis transformations.
Published structural source: AGM20, Eqs. (18)--(19), and their weighted
extension in the proof of Theorem 3.
-/

noncomputable section
open scoped BigOperators Matrix
open QuantumMaxCutEnergy QuantumMaxCutEnergy.Star QuantumMaxCutEnergy.BaselineSemantic

namespace AGMRoute.Structural

@[simp] theorem flipBit_twice {n : ℕ} (i : Fin n) (x : Basis n) :
    flipBit i (flipBit i x) = x := flipBit_involutive i x

def pauliX {n : ℕ} (i : Fin n) (ψ : Wave n) : Wave n :=
  fun x => ψ (flipBit i x)

def pauliZ {n : ℕ} (i : Fin n) (ψ : Wave n) : Wave n :=
  fun x => if x i then -ψ x else ψ x

def pauliY {n : ℕ} (i : Fin n) (ψ : Wave n) : Wave n :=
  fun x => if x i then Complex.I * ψ (flipBit i x) else -Complex.I * ψ (flipBit i x)

theorem pauliX_norm {n : ℕ} (i : Fin n) (ψ : Wave n) :
    squaredNorm (pauliX i ψ) = squaredNorm ψ := by
  exact (flipBit_involutive i).bijective.sum_comp (fun x => Complex.normSq (ψ x))

theorem pauliZ_norm {n : ℕ} (i : Fin n) (ψ : Wave n) :
    squaredNorm (pauliZ i ψ) = squaredNorm ψ := by
  apply Finset.sum_congr rfl
  intro x _
  cases h : x i <;> simp [pauliZ, h]

theorem pauliY_norm {n : ℕ} (i : Fin n) (ψ : Wave n) :
    squaredNorm (pauliY i ψ) = squaredNorm ψ := by
  calc
    squaredNorm (pauliY i ψ) = squaredNorm (pauliX i ψ) := by
      apply Finset.sum_congr rfl
      intro x _
      cases h : x i <;> simp [pauliY, pauliX, h, Complex.normSq_mul]
    _ = _ := pauliX_norm i ψ

theorem pauliX_adjoint {n : ℕ} (i : Fin n) (ψ φ : Wave n) :
    realInner (pauliX i ψ) φ = realInner ψ (pauliX i φ) := by
  have h := (flipBit_involutive i).bijective.sum_comp
    (fun x => (ψ x).re * (pauliX i φ x).re + (ψ x).im * (pauliX i φ x).im)
  simpa only [realInner, pauliX, flipBit_twice] using h

theorem pauliZ_adjoint {n : ℕ} (i : Fin n) (ψ φ : Wave n) :
    realInner (pauliZ i ψ) φ = realInner ψ (pauliZ i φ) := by
  unfold realInner
  apply Finset.sum_congr rfl
  intro x _
  cases h : x i <;> simp [pauliZ, h]

theorem pauliY_adjoint {n : ℕ} (i : Fin n) (ψ φ : Wave n) :
    realInner (pauliY i ψ) φ = realInner ψ (pauliY i φ) := by
  calc
    realInner (pauliY i ψ) φ =
        ∑ x, ((ψ (flipBit i x)).re * (pauliY i φ (flipBit i x)).re +
          (ψ (flipBit i x)).im * (pauliY i φ (flipBit i x)).im) := by
      unfold realInner
      apply Finset.sum_congr rfl
      intro x _
      have hf : (flipBit i x) i = !(x i) := by simp [flipBit]
      cases h : x i <;>
        simp [pauliY, h, hf, Complex.mul_re, Complex.mul_im] <;> ring
    _ = _ := (flipBit_involutive i).bijective.sum_comp
      (fun x => (ψ x).re * (pauliY i φ x).re + (ψ x).im * (pauliY i φ x).im)

theorem swap_eq_two_flips_of_ne {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (x : Basis n) (hbits : x i ≠ x j) :
    x ∘ Equiv.swap i j = flipBit j (flipBit i x) := by
  funext k
  by_cases hki : k = i
  · subst k
    cases hi : x i <;> cases hj : x j <;>
      simp_all [Function.comp_def, flipBit, Equiv.swap_apply_def]
  · by_cases hkj : k = j
    · subst k
      cases hi : x i <;> cases hj : x j <;>
        simp_all [Function.comp_def, flipBit, Equiv.swap_apply_def]
    · simp [Function.comp_def, flipBit, Equiv.swap_apply_def, hki, hkj]

theorem pauli_sum_swap {n : ℕ} (i j : Fin n) (hij : i ≠ j) (ψ : Wave n) :
    ψ + pauliX i (pauliX j ψ) + pauliY i (pauliY j ψ) + pauliZ i (pauliZ j ψ) =
      realScale 2 (swapWave i j ψ) := by
  funext x
  have hflipj : (flipBit i x) j = x j := by simp [flipBit, Ne.symm hij]
  by_cases hbits : x i = x j
  · have hswap : x ∘ Equiv.swap i j = x :=
      ((eq_swap_iff x i j).mpr hbits).symm
    apply Complex.ext <;>
      cases hi : x i <;> cases hj : x j <;>
      simp_all [pauliX, pauliY, pauliZ, realScale, swapWave,
        Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring
  · have hswap := swap_eq_two_flips_of_ne i j hij x hbits
    apply Complex.ext <;>
      cases hi : x i <;> cases hj : x j <;>
      simp_all [pauliX, pauliY, pauliZ, realScale, swapWave,
        Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

def realGram {n : ℕ} (v : Fin n → Wave n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => realInner (v i) (v j)

theorem realGram_posSemidef {n : ℕ} (v : Fin n → Wave n) :
    (realGram v).PosSemidef := by
  let R : Matrix (Basis n) (Fin n) ℝ := fun x i => (v i x).re
  let I : Matrix (Basis n) (Fin n) ℝ := fun x i => (v i x).im
  have heq : realGram v = Rᴴ * R + Iᴴ * I := by
    ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial]
    change (∑ x, ((v i x).re * (v j x).re + (v i x).im * (v j x).im)) =
      (∑ x, (v i x).re * (v j x).re) + ∑ x, (v i x).im * (v j x).im
    rw [Finset.sum_add_distrib]
  rw [heq]
  exact (Matrix.posSemidef_conjTranspose_mul_self R).add
    (Matrix.posSemidef_conjTranspose_mul_self I)

def pauliGram {n : ℕ} (ψ : Wave n) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 3 : ℝ) • (realGram (fun i => pauliX i ψ) +
    realGram (fun i => pauliY i ψ) + realGram (fun i => pauliZ i ψ))

theorem pauliGram_apply {n : ℕ} (ψ : Wave n) (i j : Fin n) :
    pauliGram ψ i j = (realInner (pauliX i ψ) (pauliX j ψ) +
      realInner (pauliY i ψ) (pauliY j ψ) + realInner (pauliZ i ψ) (pauliZ j ψ)) / 3 := by
  simp [pauliGram, realGram, div_eq_mul_inv, mul_comm]

theorem pauliGram_posSemidef {n : ℕ} (ψ : Wave n) :
    (pauliGram ψ).PosSemidef := by
  exact ((realGram_posSemidef (fun i => pauliX i ψ)).add
    (realGram_posSemidef (fun i => pauliY i ψ)) |>.add
    (realGram_posSemidef (fun i => pauliZ i ψ))).smul (by norm_num : (0 : ℝ) ≤ 1 / 3)

theorem pauliGram_diagonal {n : ℕ} (ψ : Wave n) (i : Fin n)
    (hψ : squaredNorm ψ = 1) : pauliGram ψ i i = 1 := by
  rw [pauliGram_apply, realInner_self, realInner_self, realInner_self,
    pauliX_norm, pauliY_norm, pauliZ_norm, hψ]
  norm_num

theorem pauliGram_energy_entry {n : ℕ} (ψ : Wave n) (i j : Fin n) (hij : i ≠ j) :
    pauliGram ψ i j = (squaredNorm ψ - 2 * pairEnergy i j ψ) / 3 := by
  have h := congrArg (fun φ => realInner ψ φ) (pauli_sum_swap i j hij ψ)
  rw [realInner_add_right, realInner_add_right, realInner_add_right,
    realInner_self, ← pauliX_adjoint, ← pauliY_adjoint, ← pauliZ_adjoint,
    realInner_scale_right] at h
  have he : pairEnergy i j ψ = squaredNorm ψ - realInner ψ (swapWave i j ψ) := by
    simp [pairEnergy, edgeAction, realInner_sub_right, realInner_self]
  rw [pauliGram_apply]
  linarith


end AGMRoute.Structural


-- Local verified source: /Users/macbookpro/prove2me-shuze/Prove2me/output/quantum-maxcut-statement/solver-2026-11-01/agm-route/AGMStructuralSDPBridge.lean


/-!
The actual QMC-to-classical-SDP structural bridge, using the platform's
existing unit-diagonal PSD and Max-Cut SDP definitions. The symmetric
weight matrix contains each undirected edge twice; the platform objective
therefore uses the standard factor 1/4.

Published source: AGM20 Eqs. (18)--(19), with the weighted extension used
in Theorem 3. This proof directly constructs a Gram matrix of Pauli features.
It makes no computational assumption and asserts no SDP solver.
-/

noncomputable section
open scoped BigOperators Matrix
open QuantumMaxCutEnergy QuantumMaxCutEnergy.Star QuantumMaxCutEnergy.BaselineSemantic
open ModernConvex.Relaxations

namespace AGMRoute.Structural

def symmetricWeights {n : ℕ} (w : Weights n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if h : i < j then (w ⟨(i, j), h⟩ : ℝ)
    else if h : j < i then (w ⟨(j, i), h⟩ : ℝ) else 0

@[simp] theorem symmetricWeights_diagonal {n : ℕ} (w : Weights n) (i : Fin n) :
    symmetricWeights w i i = 0 := by simp [symmetricWeights]

@[simp] theorem symmetricWeights_forward {n : ℕ} (w : Weights n) (e : Edge n) :
    symmetricWeights w e.val.1 e.val.2 = (w e : ℝ) := by
  rcases e with ⟨⟨i, j⟩, h⟩
  simp [symmetricWeights, h]

@[simp] theorem symmetricWeights_reverse {n : ℕ} (w : Weights n) (e : Edge n) :
    symmetricWeights w e.val.2 e.val.1 = (w e : ℝ) := by
  rcases e with ⟨⟨i, j⟩, h⟩
  simp [symmetricWeights, h, not_lt_of_gt h]

theorem maxcut_objective_edge_sum {n : ℕ} (w : Weights n)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : ∀ i j, X i j = X j i) :
    maxcutRelaxationObjective (symmetricWeights w) X =
      ∑ e : Edge n, (w e : ℝ) / 2 * (1 - X e.val.1 e.val.2) := by
  unfold maxcutRelaxationObjective
  rw [sum_off_diagonal (fun i j => symmetricWeights w i j * (1 - X i j))
    (by intro i; simp)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [symmetricWeights_forward, symmetricWeights_reverse, hX e.val.2 e.val.1]
  ring

theorem pauliGram_symm {n : ℕ} (ψ : Wave n) (i j : Fin n) :
    pauliGram ψ i j = pauliGram ψ j i := by
  simp only [pauliGram_apply]
  rw [realInner_comm (pauliX i ψ) (pauliX j ψ),
    realInner_comm (pauliY i ψ) (pauliY j ψ),
    realInner_comm (pauliZ i ψ) (pauliZ j ψ)]

theorem pauliGram_feasible {n : ℕ} (ψ : Wave n) (hψ : squaredNorm ψ = 1) :
    IsUnitDiagPSD (pauliGram ψ) :=
  ⟨pauliGram_posSemidef ψ, fun i => pauliGram_diagonal ψ i hψ⟩

theorem pauliGram_objective {n : ℕ} (w : Weights n)
    (ψ : Wave n) (hψ : squaredNorm ψ = 1) :
    maxcutRelaxationObjective (symmetricWeights w) (pauliGram ψ) =
      (energy w ψ + totalWeight w) / 3 := by
  rw [maxcut_objective_edge_sum w (pauliGram ψ) (pauliGram_symm ψ),
    energy_eq_pairEnergy]
  calc
    (∑ e : Edge n, (w e : ℝ) / 2 * (1 - pauliGram ψ e.val.1 e.val.2)) =
        ∑ e : Edge n, ((w e : ℝ) * pairEnergy e.val.1 e.val.2 ψ + (w e : ℝ)) / 3 := by
      apply Finset.sum_congr rfl
      intro e _
      rw [pauliGram_energy_entry ψ e.val.1 e.val.2 (ne_of_lt e.property), hψ]
      ring
    _ = ((∑ e : Edge n, (w e : ℝ) * pairEnergy e.val.1 e.val.2 ψ) + totalWeight w) / 3 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
      rfl

theorem energy_add_weight_le_three_sdp (G : Input) (S : ℝ)
    (hS : IsMaxcutSDPValue (symmetricWeights G.weights) S)
    (ψ : Wave G.n) (hψ : squaredNorm ψ = 1) :
    energy G.weights ψ + totalWeight G.weights ≤ 3 * S := by
  have hmem : maxcutRelaxationObjective (symmetricWeights G.weights) (pauliGram ψ) ∈
      maxcutRelaxationObjective (symmetricWeights G.weights) '' {X | IsUnitDiagPSD X} :=
    ⟨pauliGram ψ, pauliGram_feasible ψ hψ, rfl⟩
  have h := hS.1 hmem
  rw [pauliGram_objective G.weights ψ hψ] at h
  linarith

/-- Every actual classical Max-Cut SDP optimum has the structural lower
bound required by the numerical AGM reduction, including empty inputs. -/
theorem solution (G : Input) (S : ℝ)
    (hS : IsMaxcutSDPValue (symmetricWeights G.weights) S) :
    (optimum G + totalWeight G.weights) / 3 ≤ S := by
  have hO : optimum G ≤ 3 * S - totalWeight G.weights := by
    apply csSup_le (energy_values_nonempty G)
    intro v hv
    obtain ⟨ψ, hψ, rfl⟩ := hv
    have h := energy_add_weight_le_three_sdp G S hS ψ hψ
    linarith
  linarith


end AGMRoute.Structural

/-- Public formulation using only the campaign and existing SDP definitions. -/
theorem QuantumMaxCutEnergy.classical_sdp_structural_domination (G : Input) (S : ℝ)
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue
      (Matrix.of fun i j : Fin G.n =>
        if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
        else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S) :
    (QuantumMaxCutEnergy.optimum G + (∑ e, (G.weights e : ℝ))) / 3 ≤ S := by
  exact AGMRoute.Structural.solution G S hS

theorem QuantumMaxCutEnergy.classical_sdp_gram_witness (G : Input)
    (ψ : QuantumMaxCutEnergy.Wave G.n) (hψ : QuantumMaxCutEnergy.squaredNorm ψ = 1) :
    ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ModernConvex.Relaxations.IsUnitDiagPSD X ∧
      ModernConvex.Relaxations.maxcutRelaxationObjective
        (Matrix.of fun i j : Fin G.n =>
          if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
          else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) X =
        (QuantumMaxCutEnergy.energy G.weights ψ + (∑ e, (G.weights e : ℝ))) / 3 := by
  exact ⟨AGMRoute.Structural.pauliGram ψ,
    AGMRoute.Structural.pauliGram_feasible ψ hψ,
    AGMRoute.Structural.pauliGram_objective G.weights ψ hψ⟩



theorem solution (G : QuantumMaxCutEnergy.Input) (S : ℝ)
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue
      (Matrix.of fun i j : Fin G.n =>
        if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
        else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S) :
    (QuantumMaxCutEnergy.optimum G + (∑ e, (G.weights e : ℝ))) / 3 ≤ S := by
  exact QuantumMaxCutEnergy.classical_sdp_structural_domination G S hS

#print axioms solution
