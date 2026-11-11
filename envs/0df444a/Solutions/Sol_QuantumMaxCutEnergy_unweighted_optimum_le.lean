-- Prove2me | solution 1 for QuantumMaxCutEnergy.unweighted_optimum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:17:08.681217+00:00
-- url     : https://prove2.me/submissions/6e87bdf7-e591-4a9d-aec0-19a1ab240f14

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib
open scoped BigOperators

/-! Spectral upper bound `m + ⌊n/2⌋` for unweighted Quantum Max-Cut.
Source: Bakshi, Basu, Kothari, Li, arXiv:2605.14994, Theorem 3.1, combined
with the Hamming-weight block structure and the global bit-flip symmetry. -/

noncomputable section
namespace QMCSpec
open QuantumMaxCutEnergy
open Classical

/-! ### Swap operators and the real inner product -/

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

theorem shared_center_anticommutator {n : ℕ} (ψ : Wave n)
    (c i j : Fin n) (hci : c ≠ i) (hcj : c ≠ j) (hij : i ≠ j) :
    edgeAction c i (edgeAction c j ψ) + edgeAction c j (edgeAction c i ψ) =
      edgeAction c i ψ + edgeAction c j ψ - edgeAction i j ψ := by
  funext x
  have h := antisymmetrizer_pointwise ψ x c i j hci hcj hij
  simp only [edgeAction, swapWave, Pi.add_apply, Pi.sub_apply] at h ⊢
  linear_combination h

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

lemma edgeAction_symm {n : ℕ} (a b : Fin n) (ψ : Wave n) :
    edgeAction a b ψ = edgeAction b a ψ := by
  unfold edgeAction swapWave
  rw [Equiv.swap_comm a b]

lemma pairEnergy_comm {n : ℕ} (i j : Fin n) (ψ : Wave n) :
    pairEnergy i j ψ = pairEnergy j i ψ := by
  unfold pairEnergy
  rw [edgeAction_symm]

lemma energy_eq_pairEnergy {n : ℕ} (w : Weights n) (ψ : Wave n) :
    energy w ψ = ∑ e, (w e : ℝ) * pairEnergy e.val.1 e.val.2 ψ := by
  unfold energy
  apply Finset.sum_congr rfl
  intro e he
  rw [pairEnergy_eq]
  ring

lemma energy_values_nonempty (G : Input) :
    {v : ℝ | ∃ ψ : Wave G.n, squaredNorm ψ = 1 ∧ v = energy G.weights ψ}.Nonempty := by
  refine ⟨_, fun x => if x = (fun _ => false) then 1 else 0, ?_, rfl⟩
  simp [squaredNorm]

lemma inner_center_le {n : ℕ} (ψ : Wave n) (c i j : Fin n)
    (hci : c ≠ i) (hcj : c ≠ j) (hij : i ≠ j) :
    realInner (edgeAction c i ψ) (edgeAction c j ψ) ≤
      (pairEnergy c i ψ + pairEnergy c j ψ) / 2 := by
  have h := shared_center_inner ψ c i j hci hcj hij
  have hp := pairEnergy_nonneg i j ψ
  linarith

/-! ### Multiplication operators -/

def mulOp {n : ℕ} (c : Basis n → ℝ) (ψ : Wave n) : Wave n :=
  fun y => ((c y : ℝ) : ℂ) * ψ y

lemma realInner_mulOp_right {n : ℕ} (c : Basis n → ℝ) (ψ φ : Wave n) :
    realInner ψ (mulOp c φ) =
      ∑ y, c y * ((ψ y).re * (φ y).re + (ψ y).im * (φ y).im) := by
  unfold realInner mulOp
  apply Finset.sum_congr rfl
  intro y _
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

lemma realInner_mulOp_left {n : ℕ} (c : Basis n → ℝ) (ψ φ : Wave n) :
    realInner (mulOp c ψ) φ = realInner ψ (mulOp c φ) := by
  unfold realInner mulOp
  apply Finset.sum_congr rfl
  intro y _
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

lemma realInner_mulOp_self {n : ℕ} (c : Basis n → ℝ) (ψ : Wave n) :
    realInner ψ (mulOp c ψ) = ∑ y, c y * Complex.normSq (ψ y) := by
  rw [realInner_mulOp_right]
  apply Finset.sum_congr rfl
  intro y _
  rw [Complex.normSq_apply]

lemma mulOp_mulOp {n : ℕ} (c d : Basis n → ℝ) (ψ : Wave n) :
    mulOp c (mulOp d ψ) = mulOp (fun y => c y * d y) ψ := by
  funext y
  simp only [mulOp]
  push_cast
  ring

lemma edgeAction_mulOp {n : ℕ} (a b : Fin n) (c : Basis n → ℝ)
    (hc : ∀ y, c (y ∘ Equiv.swap a b) = c y) (ψ : Wave n) :
    edgeAction a b (mulOp c ψ) = mulOp c (edgeAction a b ψ) := by
  funext y
  simp only [edgeAction, swapWave, mulOp, Pi.sub_apply, hc]
  ring

/-! ### Edge sets -/

def dE {n : ℕ} (e : Edge n) (ψ : Wave n) : Wave n :=
  edgeAction e.val.1 e.val.2 ψ

def pE {n : ℕ} (e : Edge n) (ψ : Wave n) : ℝ :=
  pairEnergy e.val.1 e.val.2 ψ

def HF {n : ℕ} (F : Finset (Edge n)) (ψ : Wave n) : Wave n :=
  ∑ e ∈ F, dE e ψ

def verts {n : ℕ} (F : Finset (Edge n)) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ∃ e ∈ F, v = e.val.1 ∨ v = e.val.2)

def cnt {n : ℕ} (F : Finset (Edge n)) (y : Basis n) : ℕ :=
  ((verts F).filter (fun v => y v = true)).card

def WF {n : ℕ} (F : Finset (Edge n)) (y : Basis n) : ℝ :=
  (F.card : ℝ) + (cnt F y : ℝ)

def WF2 {n : ℕ} (F : Finset (Edge n)) (y : Basis n) : ℝ :=
  (F.card : ℝ) + ((verts F).card : ℝ) - (cnt F y : ℝ)

lemma mem_verts {n : ℕ} (F : Finset (Edge n)) (v : Fin n) :
    v ∈ verts F ↔ ∃ e ∈ F, v = e.val.1 ∨ v = e.val.2 := by
  simp [verts]

lemma mem_verts_left {n : ℕ} {F : Finset (Edge n)} {e : Edge n} (he : e ∈ F) :
    e.val.1 ∈ verts F := (mem_verts F _).mpr ⟨e, he, Or.inl rfl⟩

lemma mem_verts_right {n : ℕ} {F : Finset (Edge n)} {e : Edge n} (he : e ∈ F) :
    e.val.2 ∈ verts F := (mem_verts F _).mpr ⟨e, he, Or.inr rfl⟩

lemma verts_mono {n : ℕ} {F' F : Finset (Edge n)} (h : F' ⊆ F) :
    verts F' ⊆ verts F := by
  intro v hv
  rw [mem_verts] at hv ⊢
  obtain ⟨e, he, hve⟩ := hv
  exact ⟨e, h he, hve⟩

lemma swap_mem_verts {n : ℕ} {F : Finset (Edge n)} {a b v : Fin n}
    (ha : a ∈ verts F) (hb : b ∈ verts F) (hv : v ∈ verts F) :
    Equiv.swap a b v ∈ verts F := by
  rw [Equiv.swap_apply_def]
  split_ifs <;> assumption

lemma cnt_swap {n : ℕ} (F : Finset (Edge n)) {a b : Fin n}
    (ha : a ∈ verts F) (hb : b ∈ verts F) (y : Basis n) :
    cnt F (y ∘ Equiv.swap a b) = cnt F y := by
  unfold cnt
  apply Finset.card_bij' (fun v _ => Equiv.swap a b v) (fun v _ => Equiv.swap a b v)
  · intro v hv
    rw [Finset.mem_filter] at hv ⊢
    exact ⟨swap_mem_verts ha hb hv.1, hv.2⟩
  · intro v hv
    rw [Finset.mem_filter] at hv ⊢
    refine ⟨swap_mem_verts ha hb hv.1, ?_⟩
    simpa using hv.2
  · intro v _
    simp
  · intro v _
    simp

lemma WF_swap {n : ℕ} (F : Finset (Edge n)) {e : Edge n} (he : e ∈ F) (y : Basis n) :
    WF F (y ∘ Equiv.swap e.val.1 e.val.2) = WF F y := by
  unfold WF
  rw [cnt_swap F (mem_verts_left he) (mem_verts_right he)]

lemma WF_nonneg {n : ℕ} (F : Finset (Edge n)) (y : Basis n) : 0 ≤ WF F y := by
  unfold WF
  positivity

lemma WF_pos {n : ℕ} {F : Finset (Edge n)} (hF : F.Nonempty) (y : Basis n) :
    0 < WF F y := by
  unfold WF
  have h1 : (0 : ℝ) < (F.card : ℝ) := by exact_mod_cast hF.card_pos
  have h2 : (0 : ℝ) ≤ (cnt F y : ℝ) := Nat.cast_nonneg _
  linarith

lemma HF_apply {n : ℕ} (F : Finset (Edge n)) (ψ : Wave n) (y : Basis n) :
    HF F ψ y = ∑ e ∈ F, dE e ψ y := by
  unfold HF
  rw [Finset.sum_apply]

lemma HF_mulOp {n : ℕ} (F : Finset (Edge n)) (c : Basis n → ℝ)
    (hc : ∀ e ∈ F, ∀ y, c (y ∘ Equiv.swap e.val.1 e.val.2) = c y) (ψ : Wave n) :
    HF F (mulOp c ψ) = mulOp c (HF F ψ) := by
  funext y
  rw [HF_apply]
  show _ = ((c y : ℝ) : ℂ) * HF F ψ y
  rw [HF_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  exact congrFun (edgeAction_mulOp e.val.1 e.val.2 c (hc e he) ψ) y

lemma realInner_HF_right {n : ℕ} (F : Finset (Edge n)) (ψ φ : Wave n) :
    realInner ψ (HF F φ) = ∑ e ∈ F, realInner ψ (dE e φ) :=
  realInner_sum_right F ψ (fun e => dE e φ)

lemma realInner_HF_left {n : ℕ} (F : Finset (Edge n)) (ψ φ : Wave n) :
    realInner (HF F ψ) φ = ∑ e ∈ F, realInner (dE e ψ) φ :=
  realInner_sum_left F (fun e => dE e ψ) φ

lemma dE_half {n : ℕ} (e : Edge n) (ψ φ : Wave n) :
    realInner (dE e ψ) (dE e φ) = 2 * realInner (dE e ψ) φ := by
  unfold dE
  rw [← edgeAction_adjoint, edgeAction_twice, realInner_scale_left]

lemma dE_eq_zero {n : ℕ} (e : Edge n) (ψ : Wave n) (y : Basis n)
    (h : y e.val.1 = y e.val.2) : dE e ψ y = 0 := by
  simp [dE, edgeAction, swapWave, same_swap y _ _ h]

lemma dE_mulOp_WF {n : ℕ} (F : Finset (Edge n)) (e : Edge n) (he : e ∈ F) (ψ : Wave n) :
    dE e (mulOp (WF F) ψ) = mulOp (WF F) (dE e ψ) :=
  edgeAction_mulOp _ _ _ (WF_swap F he) ψ

/-! ### Relative position of two edges -/

def disj {n : ℕ} (e f : Edge n) : Prop :=
  e.val.1 ≠ f.val.1 ∧ e.val.1 ≠ f.val.2 ∧ e.val.2 ≠ f.val.1 ∧ e.val.2 ≠ f.val.2

def adj {n : ℕ} (e f : Edge n) : Prop := f ≠ e ∧ ¬ disj e f

lemma disj_symm {n : ℕ} (e f : Edge n) (h : disj e f) : disj f e :=
  ⟨h.1.symm, h.2.2.1.symm, h.2.1.symm, h.2.2.2.symm⟩

lemma adj_symm {n : ℕ} (e f : Edge n) (h : adj e f) : adj f e :=
  ⟨h.1.symm, fun hd => h.2 (disj_symm f e hd)⟩

lemma not_disj_self {n : ℕ} (e : Edge n) : ¬ disj e e := fun h => h.1 rfl

def Fd {n : ℕ} (F : Finset (Edge n)) (e : Edge n) : Finset (Edge n) :=
  F.filter (disj e)

def Ft {n : ℕ} (F : Finset (Edge n)) (e : Edge n) : Finset (Edge n) :=
  F.filter (adj e)

lemma Fd_ssubset {n : ℕ} (F : Finset (Edge n)) (e : Edge n) (he : e ∈ F) :
    Fd F e ⊂ F :=
  Finset.filter_ssubset.mpr ⟨e, he, not_disj_self e⟩

lemma e_notMem_Ft {n : ℕ} (F : Finset (Edge n)) (e : Edge n) : e ∉ Ft F e := by
  intro h
  exact (Finset.mem_filter.mp h).2.1 rfl

lemma filter_not_disj {n : ℕ} (F : Finset (Edge n)) (e : Edge n) (he : e ∈ F) :
    F.filter (fun f => ¬ disj e f) = insert e (Ft F e) := by
  ext f
  simp only [Ft, adj, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hf, hd⟩
    by_cases h : f = e
    · exact Or.inl h
    · exact Or.inr ⟨hf, h, hd⟩
  · rintro (h | ⟨hf, _, hd⟩)
    · rw [h]
      exact ⟨he, not_disj_self e⟩
    · exact ⟨hf, hd⟩

lemma card_split {n : ℕ} (F : Finset (Edge n)) (e : Edge n) (he : e ∈ F) :
    F.card = 1 + (Fd F e).card + (Ft F e).card := by
  have h := Finset.card_filter_add_card_filter_not (s := F) (disj e)
  rw [filter_not_disj F e he, Finset.card_insert_of_notMem (e_notMem_Ft F e)] at h
  unfold Fd
  omega

lemma sum_split {n : ℕ} (F : Finset (Edge n)) (e : Edge n) (he : e ∈ F)
    (g : Edge n → ℝ) :
    ∑ f ∈ F, g f = g e + ∑ f ∈ Fd F e, g f + ∑ f ∈ Ft F e, g f := by
  rw [← Finset.sum_filter_add_sum_filter_not F (disj e) g, filter_not_disj F e he,
    Finset.sum_insert (e_notMem_Ft F e)]
  unfold Fd
  ring

lemma swap_comm_disj {α β : Type*} [DecidableEq α] (x : α → β) (a b c d : α)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (x ∘ Equiv.swap c d) ∘ Equiv.swap a b = (x ∘ Equiv.swap a b) ∘ Equiv.swap c d := by
  have hca : c ≠ a := hac.symm
  have hda : d ≠ a := had.symm
  have hcb : c ≠ b := hbc.symm
  have hdb : d ≠ b := hbd.symm
  funext k
  by_cases hka : k = a <;> by_cases hkb : k = b <;> by_cases hkc : k = c <;>
    by_cases hkd : k = d <;>
    simp_all [Function.comp_apply, Equiv.swap_apply_def]

lemma dE_comm_disj {n : ℕ} (e f : Edge n) (h : disj e f) (ψ : Wave n) :
    dE e (dE f ψ) = dE f (dE e ψ) := by
  funext x
  have hs := swap_comm_disj x f.val.1 f.val.2 e.val.1 e.val.2
    h.1.symm h.2.2.1.symm h.2.1.symm h.2.2.2.symm
  simp only [dE, edgeAction, swapWave, Pi.sub_apply]
  rw [hs]
  ring

lemma inner_adj_le {n : ℕ} (ψ : Wave n) (e f : Edge n) (hne : f ≠ e)
    (hnd : ¬ disj e f) :
    realInner (dE e ψ) (dE f ψ) ≤ (pE e ψ + pE f ψ) / 2 := by
  obtain ⟨⟨i, j⟩, hij⟩ := e
  obtain ⟨⟨k, l⟩, hkl⟩ := f
  change i < j at hij
  change k < l at hkl
  have hne' : ¬ (k = i ∧ l = j) := by
    rintro ⟨h1, h2⟩
    subst h1
    subst h2
    exact hne rfl
  have hcases : i = k ∨ i = l ∨ j = k ∨ j = l := by
    by_contra h
    exact hnd ⟨fun h1 => h (Or.inl h1), fun h2 => h (Or.inr (Or.inl h2)),
      fun h3 => h (Or.inr (Or.inr (Or.inl h3))),
      fun h4 => h (Or.inr (Or.inr (Or.inr h4)))⟩
  show realInner (edgeAction i j ψ) (edgeAction k l ψ) ≤
    (pairEnergy i j ψ + pairEnergy k l ψ) / 2
  rcases hcases with h | h | h | h
  · subst h
    exact inner_center_le ψ i j l (ne_of_lt hij) (ne_of_lt hkl)
      (fun h => hne' ⟨rfl, h.symm⟩)
  · subst h
    rw [edgeAction_symm k i, pairEnergy_comm k i]
    exact inner_center_le ψ i j k (ne_of_lt hij) (ne_of_gt hkl)
      (ne_of_gt (hkl.trans hij))
  · subst h
    rw [edgeAction_symm i j, pairEnergy_comm i j]
    exact inner_center_le ψ j i l (ne_of_gt hij) (ne_of_lt hkl)
      (ne_of_lt (hij.trans hkl))
  · subst h
    rw [edgeAction_symm i j, pairEnergy_comm i j, edgeAction_symm k j,
      pairEnergy_comm k j]
    exact inner_center_le ψ j i k (ne_of_gt hij) (ne_of_gt hkl)
      (fun h => hne' ⟨h.symm, rfl⟩)

lemma double_count {ι : Type*} (F : Finset ι) (r : ι → ι → Prop)
    (hr : ∀ e f, r e f → r f e) (p : ι → ℝ) :
    ∑ e ∈ F, ∑ f ∈ F.filter (r e), (p e + p f) / 2 =
      ∑ e ∈ F, ((F.filter (r e)).card : ℝ) * p e := by
  have h1 : ∀ e, ∑ f ∈ F.filter (r e), (p e + p f) / 2 =
      ∑ f ∈ F, (if r e f then p e / 2 else 0) +
        ∑ f ∈ F, (if r e f then p f / 2 else 0) := by
    intro e
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro f _
    split_ifs <;> ring
  have h2 : ∀ e, ((F.filter (r e)).card : ℝ) * p e =
      2 * ∑ f ∈ F, (if r e f then p e / 2 else 0) := by
    intro e
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  have h3 : ∑ e ∈ F, ∑ f ∈ F, (if r e f then p f / 2 else 0) =
      ∑ e ∈ F, ∑ f ∈ F, (if r e f then p e / 2 else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f _
    have hiff : r f e ↔ r e f := ⟨hr f e, hr e f⟩
    simp only [hiff]
  simp only [h1, h2]
  rw [Finset.sum_add_distrib, h3, ← Finset.mul_sum]
  ring

lemma cnt_Fd_lt {n : ℕ} (F : Finset (Edge n)) (e : Edge n) (he : e ∈ F)
    (y : Basis n) (hy : y e.val.1 ≠ y e.val.2) :
    cnt (Fd F e) y + 1 ≤ cnt F y := by
  have hnot : ∀ v, (v = e.val.1 ∨ v = e.val.2) → v ∉ verts (Fd F e) := by
    intro v hv hmem
    rw [mem_verts] at hmem
    obtain ⟨f, hf, hvf⟩ := hmem
    obtain ⟨h1, h2, h3, h4⟩ := (Finset.mem_filter.mp hf).2
    rcases hv with hv | hv <;> rcases hvf with h | h
    · exact h1 (hv.symm.trans h)
    · exact h2 (hv.symm.trans h)
    · exact h3 (hv.symm.trans h)
    · exact h4 (hv.symm.trans h)
  obtain ⟨v, hv, hyv, hvn⟩ :
      ∃ v, v ∈ verts F ∧ y v = true ∧ v ∉ verts (Fd F e) := by
    cases h1 : y e.val.1 <;> cases h2 : y e.val.2
    · exact absurd (h1.trans h2.symm) hy
    · exact ⟨e.val.2, mem_verts_right he, h2, hnot _ (Or.inr rfl)⟩
    · exact ⟨e.val.1, mem_verts_left he, h1, hnot _ (Or.inl rfl)⟩
    · exact absurd (h1.trans h2.symm) hy
  unfold cnt
  have hvn' : v ∉ (verts (Fd F e)).filter (fun v => y v = true) := by
    intro h
    exact hvn (Finset.mem_filter.mp h).1
  rw [← Finset.card_insert_of_notMem hvn']
  apply Finset.card_le_card
  intro u hu
  rw [Finset.mem_insert] at hu
  rcases hu with hu | hu
  · rw [hu]
    exact Finset.mem_filter.mpr ⟨hv, hyv⟩
  · rw [Finset.mem_filter] at hu ⊢
    exact ⟨verts_mono (Finset.filter_subset _ _) hu.1, hu.2⟩

/-! ### The key inequality and its consequences -/

def Kprop {n : ℕ} (F : Finset (Edge n)) : Prop :=
  ∀ ψ : Wave n, realInner (HF F ψ) (HF F ψ) ≤ realInner (HF F ψ) (mulOp (WF F) ψ)

def B1prop {n : ℕ} (F : Finset (Edge n)) : Prop :=
  ∀ ψ : Wave n, realInner ψ (HF F ψ) ≤ realInner ψ (mulOp (WF F) ψ)

lemma weight_step {n : ℕ} (F : Finset (Edge n)) (e : Edge n) (he : e ∈ F)
    (ψ : Wave n) :
    2 * pE e ψ + (1 / 2) * realInner (dE e ψ) (mulOp (WF (Fd F e)) (dE e ψ)) +
        ((Ft F e).card : ℝ) * pE e ψ ≤
      (1 / 2) * realInner (dE e ψ) (mulOp (WF F) (dE e ψ)) := by
  have hp : pE e ψ = (1 / 2) * ∑ y, Complex.normSq (dE e ψ y) := by
    have h := edgeAction_squaredNorm e.val.1 e.val.2 ψ
    unfold squaredNorm at h
    unfold pE dE
    linarith
  rw [realInner_mulOp_self, realInner_mulOp_self, hp]
  have key : ∀ y, (2 + ((Ft F e).card : ℝ) + WF (Fd F e) y) *
        Complex.normSq (dE e ψ y) ≤ WF F y * Complex.normSq (dE e ψ y) := by
    intro y
    by_cases h : y e.val.1 = y e.val.2
    · rw [dE_eq_zero e ψ y h]
      simp
    · apply mul_le_mul_of_nonneg_right _ (Complex.normSq_nonneg _)
      have h1 := cnt_Fd_lt F e he y h
      have h2 := card_split F e he
      have h1' : (cnt (Fd F e) y : ℝ) + 1 ≤ (cnt F y : ℝ) := by exact_mod_cast h1
      have h2' : (F.card : ℝ) = 1 + ((Fd F e).card : ℝ) + ((Ft F e).card : ℝ) := by
        exact_mod_cast h2
      unfold WF
      linarith
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => key y)
  simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  linarith

lemma K_step {n : ℕ} (F : Finset (Edge n)) (ih : ∀ F' ⊂ F, B1prop F') :
    Kprop F := by
  intro ψ
  have hL : realInner (HF F ψ) (HF F ψ) =
      ∑ e ∈ F, ∑ f ∈ F, realInner (dE e ψ) (dE f ψ) := by
    rw [realInner_HF_left]
    apply Finset.sum_congr rfl
    intro e _
    rw [realInner_HF_right]
  have hR : realInner (HF F ψ) (mulOp (WF F) ψ) =
      ∑ e ∈ F, (1 / 2) * realInner (dE e ψ) (mulOp (WF F) (dE e ψ)) := by
    rw [realInner_HF_left]
    apply Finset.sum_congr rfl
    intro e he
    rw [← dE_mulOp_WF F e he ψ, dE_half]
    ring
  have hrow : ∀ e ∈ F, ∑ f ∈ F, realInner (dE e ψ) (dE f ψ) ≤
      2 * pE e ψ + (1 / 2) * realInner (dE e ψ) (mulOp (WF (Fd F e)) (dE e ψ)) +
        ∑ f ∈ Ft F e, (pE e ψ + pE f ψ) / 2 := by
    intro e he
    rw [sum_split F e he]
    have h1 : realInner (dE e ψ) (dE e ψ) = 2 * pE e ψ := by
      rw [realInner_self]
      exact edgeAction_squaredNorm _ _ _
    have h2 : ∑ f ∈ Fd F e, realInner (dE e ψ) (dE f ψ) ≤
        (1 / 2) * realInner (dE e ψ) (mulOp (WF (Fd F e)) (dE e ψ)) := by
      have hb := ih (Fd F e) (Fd_ssubset F e he) (dE e ψ)
      have hEq : ∑ f ∈ Fd F e, realInner (dE e ψ) (dE f ψ) =
          (1 / 2) * realInner (dE e ψ) (HF (Fd F e) (dE e ψ)) := by
        rw [realInner_HF_right, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro f hf
        have hd : disj e f := (Finset.mem_filter.mp hf).2
        rw [← dE_comm_disj e f hd ψ, dE_half]
        ring
      rw [hEq]
      linarith
    have h3 : ∑ f ∈ Ft F e, realInner (dE e ψ) (dE f ψ) ≤
        ∑ f ∈ Ft F e, (pE e ψ + pE f ψ) / 2 := by
      apply Finset.sum_le_sum
      intro f hf
      obtain ⟨_, hne, hnd⟩ := Finset.mem_filter.mp hf
      exact inner_adj_le ψ e f hne hnd
    linarith
  have hdc : ∑ e ∈ F, ∑ f ∈ Ft F e, (pE e ψ + pE f ψ) / 2 =
      ∑ e ∈ F, ((Ft F e).card : ℝ) * pE e ψ :=
    double_count F adj adj_symm (fun e => pE e ψ)
  rw [hL, hR]
  calc ∑ e ∈ F, ∑ f ∈ F, realInner (dE e ψ) (dE f ψ)
      ≤ ∑ e ∈ F, (2 * pE e ψ +
          (1 / 2) * realInner (dE e ψ) (mulOp (WF (Fd F e)) (dE e ψ)) +
          ∑ f ∈ Ft F e, (pE e ψ + pE f ψ) / 2) := Finset.sum_le_sum hrow
    _ = ∑ e ∈ F, (2 * pE e ψ +
          (1 / 2) * realInner (dE e ψ) (mulOp (WF (Fd F e)) (dE e ψ)) +
          ((Ft F e).card : ℝ) * pE e ψ) := by
        rw [Finset.sum_add_distrib, hdc, ← Finset.sum_add_distrib]
    _ ≤ _ := Finset.sum_le_sum (fun e he => weight_step F e he ψ)

lemma K_imp_B1_aux {n : ℕ} (F : Finset (Edge n)) (hK : Kprop F)
    (s : Basis n → ℝ) (hss : ∀ y, s y * s y = WF F y)
    (hsinv : ∀ e ∈ F, ∀ y, s (y ∘ Equiv.swap e.val.1 e.val.2) = s y)
    (χ : Wave n) :
    realInner (mulOp s χ) (HF F (mulOp s χ)) ≤
      realInner (mulOp s χ) (mulOp (WF F) (mulOp s χ)) := by
  have e1 : ∀ φ : Wave n, mulOp s (mulOp s φ) = mulOp (WF F) φ := by
    intro φ
    rw [mulOp_mulOp]
    congr 1
    funext y
    exact hss y
  have e2 : ∀ φ : Wave n, mulOp (WF F) (mulOp s φ) = mulOp s (mulOp (WF F) φ) := by
    intro φ
    rw [mulOp_mulOp, mulOp_mulOp]
    congr 1
    funext y
    ring
  have hl : realInner (mulOp s χ) (HF F (mulOp s χ)) =
      realInner (HF F χ) (mulOp (WF F) χ) := by
    rw [HF_mulOp F s hsinv, realInner_mulOp_left, e1, realInner_comm,
      realInner_mulOp_left]
  have hr : realInner (mulOp s χ) (mulOp (WF F) (mulOp s χ)) =
      realInner (mulOp (WF F) χ) (mulOp (WF F) χ) := by
    rw [e2, realInner_mulOp_left, e1, realInner_comm, realInner_mulOp_left]
  rw [hl, hr]
  have h1 := hK χ
  have h2 := realInner_nonneg (HF F χ - mulOp (WF F) χ)
  simp only [realInner_sub_left, realInner_sub_right] at h2
  have h3 := realInner_comm (mulOp (WF F) χ) (HF F χ)
  linarith

lemma K_imp_B1 {n : ℕ} (F : Finset (Edge n)) (hK : Kprop F) : B1prop F := by
  intro ψ
  rcases F.eq_empty_or_nonempty with hF | hF
  · subst hF
    have h0 : HF (∅ : Finset (Edge n)) ψ = 0 := by simp [HF]
    rw [h0, realInner_zero_right, realInner_mulOp_self]
    exact Finset.sum_nonneg fun y _ =>
      mul_nonneg (WF_nonneg _ y) (Complex.normSq_nonneg _)
  · have hss : ∀ y, Real.sqrt (WF F y) * Real.sqrt (WF F y) = WF F y :=
      fun y => Real.mul_self_sqrt (WF_nonneg F y)
    have hsinv : ∀ e ∈ F, ∀ y,
        Real.sqrt (WF F (y ∘ Equiv.swap e.val.1 e.val.2)) = Real.sqrt (WF F y) := by
      intro e he y
      rw [WF_swap F he]
    have h := K_imp_B1_aux F hK (fun y => Real.sqrt (WF F y)) hss hsinv
      (mulOp (fun y => (Real.sqrt (WF F y))⁻¹) ψ)
    have hψ : mulOp (fun y => Real.sqrt (WF F y))
        (mulOp (fun y => (Real.sqrt (WF F y))⁻¹) ψ) = ψ := by
      rw [mulOp_mulOp]
      funext y
      have hne : Real.sqrt (WF F y) ≠ 0 := (Real.sqrt_pos.mpr (WF_pos hF y)).ne'
      simp only [mulOp]
      rw [mul_inv_cancel₀ hne]
      simp
    rw [hψ] at h
    exact h

theorem B1_all {n : ℕ} (F : Finset (Edge n)) : B1prop F := by
  induction F using Finset.strongInduction with
  | H F ih => exact K_imp_B1 F (K_step F ih)

/-! ### Global bit flip -/

def flipB {n : ℕ} (y : Basis n) : Basis n := fun v => !y v

def flipW {n : ℕ} (ψ : Wave n) : Wave n := fun y => ψ (flipB y)

lemma flipB_flipB {n : ℕ} (y : Basis n) : flipB (flipB y) = y := by
  funext v
  simp [flipB]

def flipEquiv {n : ℕ} : Basis n ≃ Basis n where
  toFun := flipB
  invFun := flipB
  left_inv := flipB_flipB
  right_inv := flipB_flipB

lemma realInner_flip {n : ℕ} (ψ φ : Wave n) :
    realInner (flipW ψ) (flipW φ) = realInner ψ φ := by
  unfold realInner
  exact (flipEquiv (n := n)).sum_comp
    (fun x => (ψ x).re * (φ x).re + (ψ x).im * (φ x).im)

lemma HF_flip {n : ℕ} (F : Finset (Edge n)) (ψ : Wave n) :
    HF F (flipW ψ) = flipW (HF F ψ) := by
  funext y
  rw [HF_apply]
  show _ = HF F ψ (flipB y)
  rw [HF_apply]
  rfl

lemma cnt_flip {n : ℕ} (F : Finset (Edge n)) (y : Basis n) :
    cnt F y + cnt F (flipB y) = (verts F).card := by
  unfold cnt
  have h : (verts F).filter (fun v => flipB y v = true) =
      (verts F).filter (fun v => ¬ (y v = true)) := by
    apply Finset.filter_congr
    intro v _
    simp [flipB]
  rw [h]
  exact Finset.card_filter_add_card_filter_not (s := verts F) (fun v => y v = true)

lemma B2 {n : ℕ} (F : Finset (Edge n)) (hB : B1prop F) (ψ : Wave n) :
    realInner ψ (HF F ψ) ≤ realInner ψ (mulOp (WF2 F) ψ) := by
  have h := hB (flipW ψ)
  have hm : mulOp (WF F) (flipW ψ) = flipW (mulOp (WF2 F) ψ) := by
    funext y
    show ((WF F y : ℝ) : ℂ) * ψ (flipB y) = ((WF2 F (flipB y) : ℝ) : ℂ) * ψ (flipB y)
    have hW : WF F y = WF2 F (flipB y) := by
      unfold WF WF2
      have hc := cnt_flip F y
      have hc' : (cnt F y : ℝ) + (cnt F (flipB y) : ℝ) = ((verts F).card : ℝ) := by
        exact_mod_cast hc
      linarith
    rw [hW]
  rw [HF_flip, hm, realInner_flip, realInner_flip] at h
  exact h

/-! ### Combining the two sector bounds -/

lemma normSq_mulOp {n : ℕ} (c : Basis n → ℝ) (ψ : Wave n) (y : Basis n) :
    Complex.normSq (mulOp c ψ y) = c y * c y * Complex.normSq (ψ y) := by
  simp [mulOp, Complex.normSq_mul, Complex.normSq_ofReal]

lemma B3 {n : ℕ} (F : Finset (Edge n)) (hB : B1prop F) (ψ : Wave n) :
    realInner ψ (HF F ψ) ≤
      ((F.card : ℝ) + (((verts F).card / 2 : ℕ) : ℝ)) * squaredNorm ψ := by
  let P : Basis n → ℝ := fun y => if 2 * cnt F y ≤ (verts F).card then 1 else 0
  let Q : Basis n → ℝ := fun y => if 2 * cnt F y ≤ (verts F).card then 0 else 1
  have hPinv : ∀ e ∈ F, ∀ y, P (y ∘ Equiv.swap e.val.1 e.val.2) = P y := by
    intro e he y
    simp only [P, cnt_swap F (mem_verts_left he) (mem_verts_right he)]
  have hQinv : ∀ e ∈ F, ∀ y, Q (y ∘ Equiv.swap e.val.1 e.val.2) = Q y := by
    intro e he y
    simp only [Q, cnt_swap F (mem_verts_left he) (mem_verts_right he)]
  have hPQ : ∀ y, P y * P y + Q y * Q y = 1 := by
    intro y
    simp only [P, Q]
    split_ifs <;> norm_num
  have hsplit : realInner ψ (HF F ψ) =
      realInner (mulOp P ψ) (HF F (mulOp P ψ)) +
        realInner (mulOp Q ψ) (HF F (mulOp Q ψ)) := by
    rw [HF_mulOp F P hPinv, HF_mulOp F Q hQinv, realInner_mulOp_left,
      realInner_mulOp_left, mulOp_mulOp, mulOp_mulOp, realInner_mulOp_right,
      realInner_mulOp_right, ← Finset.sum_add_distrib]
    unfold realInner
    apply Finset.sum_congr rfl
    intro y _
    rw [← add_mul, hPQ y, one_mul]
  have hP : realInner (mulOp P ψ) (HF F (mulOp P ψ)) ≤
      ∑ y, ((F.card : ℝ) + (((verts F).card / 2 : ℕ) : ℝ)) *
        (P y * P y * Complex.normSq (ψ y)) := by
    refine (hB (mulOp P ψ)).trans ?_
    rw [realInner_mulOp_self]
    apply Finset.sum_le_sum
    intro y _
    rw [normSq_mulOp]
    by_cases hy : 2 * cnt F y ≤ (verts F).card
    · apply mul_le_mul_of_nonneg_right _
        (mul_nonneg (mul_self_nonneg _) (Complex.normSq_nonneg _))
      unfold WF
      have hle : cnt F y ≤ (verts F).card / 2 := by omega
      have hle' : (cnt F y : ℝ) ≤ (((verts F).card / 2 : ℕ) : ℝ) := by
        exact_mod_cast hle
      linarith
    · have hP0 : P y = 0 := by simp only [P, if_neg hy]
      rw [hP0]
      simp
  have hQ : realInner (mulOp Q ψ) (HF F (mulOp Q ψ)) ≤
      ∑ y, ((F.card : ℝ) + (((verts F).card / 2 : ℕ) : ℝ)) *
        (Q y * Q y * Complex.normSq (ψ y)) := by
    refine (B2 F hB (mulOp Q ψ)).trans ?_
    rw [realInner_mulOp_self]
    apply Finset.sum_le_sum
    intro y _
    rw [normSq_mulOp]
    by_cases hy : 2 * cnt F y ≤ (verts F).card
    · have hQ0 : Q y = 0 := by simp only [Q, if_pos hy]
      rw [hQ0]
      simp
    · apply mul_le_mul_of_nonneg_right _
        (mul_nonneg (mul_self_nonneg _) (Complex.normSq_nonneg _))
      unfold WF2
      have hle : (verts F).card ≤ cnt F y + (verts F).card / 2 := by omega
      have hle' : ((verts F).card : ℝ) ≤
          (cnt F y : ℝ) + (((verts F).card / 2 : ℕ) : ℝ) := by
        exact_mod_cast hle
      linarith
  rw [hsplit]
  refine (add_le_add hP hQ).trans (le_of_eq ?_)
  rw [← Finset.sum_add_distrib]
  unfold squaredNorm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [← mul_add, ← add_mul, hPQ y, one_mul]

/-! ### Conclusion -/

lemma energy_bound {n : ℕ} (w : Weights n) (hw : ∀ e, w e = 0 ∨ w e = 1)
    (ψ : Wave n) (hψ : squaredNorm ψ = 1) :
    energy w ψ ≤ (∑ e, (w e : ℝ)) + ((n / 2 : ℕ) : ℝ) := by
  have hE : energy w ψ =
      realInner ψ (HF (Finset.univ.filter (fun e => w e = 1)) ψ) := by
    rw [energy_eq_pairEnergy, realInner_HF_right, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    rcases hw e with h | h <;> simp [h, pairEnergy, dE]
  have hS : ∑ e, (w e : ℝ) =
      ((Finset.univ.filter (fun e => w e = 1)).card : ℝ) := by
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro e _
    rcases hw e with h | h <;> simp [h]
  have h3 := B3 _ (B1_all (Finset.univ.filter (fun e => w e = 1))) ψ
  rw [hψ, mul_one] at h3
  have hV : (((verts (Finset.univ.filter (fun e => w e = 1))).card / 2 : ℕ) : ℝ) ≤
      ((n / 2 : ℕ) : ℝ) := by
    have hle : (verts (Finset.univ.filter (fun e => w e = 1))).card ≤ n := by
      simpa using Finset.card_le_univ (verts (Finset.univ.filter (fun e => w e = 1)))
    exact_mod_cast Nat.div_le_div_right hle
  rw [hE, hS]
  linarith

end QMCSpec
end

theorem solution {n : ℕ}
    (w : QuantumMaxCutEnergy.Weights n) (hw : ∀ e, w e = 0 ∨ w e = 1) :
    QuantumMaxCutEnergy.optimum ⟨n, w⟩ ≤ (∑ e, (w e : ℝ)) + ((n / 2 : ℕ) : ℝ) := by
  apply csSup_le (QMCSpec.energy_values_nonempty ⟨n, w⟩)
  rintro v ⟨ψ, hψ, rfl⟩
  exact QMCSpec.energy_bound w hw ψ hψ
