-- Prove2me | solution 1 for QuantumMaxCutEnergy.pmatch_state_energy_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:41:42.792504+00:00
-- url     : https://prove2.me/submissions/07354ef6-1c99-4a80-a011-256ea886570f

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel

open scoped BigOperators

noncomputable section
open scoped BigOperators
open QuantumMaxCutEnergy
namespace QMCPMatch.BlochFoundation

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



def ket {n : ℕ} (b : Basis n) : Wave n := fun x => if x = b then 1 else 0

def cutWeight {n : ℕ} (w : Weights n) (b : Basis n) : ℝ :=
  ∑ e, if b e.val.1 = b e.val.2 then 0 else (w e : ℝ)

lemma squaredNorm_ket {n : ℕ} (b : Basis n) : squaredNorm (ket b) = 1 := by
  classical
  simp [squaredNorm, ket]



lemma eq_swap_iff {n : ℕ} (b : Basis n) (i j : Fin n) :
    (b = b ∘ Equiv.swap i j) ↔ b i = b j := by
  constructor
  · intro h
    simpa using congrFun h i
  · intro h
    funext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp_all [Equiv.swap_apply_def]



def flipBit {n : ℕ} (i : Fin n) (b : Basis n) : Basis n :=
  Function.update b i (!(b i))

lemma flipBit_involutive {n : ℕ} (i : Fin n) : Function.Involutive (flipBit i) := by
  intro b
  funext k
  by_cases hk : k = i
  · subst k
    simp [flipBit]
  · simp [flipBit, hk]



def swapWave {n : ℕ} (a b : Fin n) (ψ : Wave n) : Wave n :=
  fun x => ψ (x ∘ Equiv.swap a b)

def edgeAction {n : ℕ} (a b : Fin n) (ψ : Wave n) : Wave n :=
  ψ - swapWave a b ψ



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
  norm_num <;> ring

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



lemma energy_eq_pairEnergy {n : ℕ} (w : Weights n) (ψ : Wave n) :
    energy w ψ = ∑ e, (w e : ℝ) * pairEnergy e.val.1 e.val.2 ψ := by
  unfold energy
  apply Finset.sum_congr rfl
  intro e he
  rw [pairEnergy_eq]
  ring



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


end QMCPMatch.BlochFoundation

open QMCPMatch.BlochFoundation
namespace QMCPMatch.BlochStructural

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


theorem pauli_correlation_sum {n : ℕ} (ψ : Wave n) (i j : Fin n) (hij : i ≠ j) :
    realInner (pauliX i ψ) (pauliX j ψ) + realInner (pauliY i ψ) (pauliY j ψ) +
      realInner (pauliZ i ψ) (pauliZ j ψ) = squaredNorm ψ - 2 * pairEnergy i j ψ := by
  have h := congrArg (fun φ => realInner ψ φ) (pauli_sum_swap i j hij ψ)
  rw [realInner_add_right, realInner_add_right, realInner_add_right,
    realInner_self, ← pauliX_adjoint, ← pauliY_adjoint, ← pauliZ_adjoint,
    realInner_scale_right] at h
  have he : pairEnergy i j ψ = squaredNorm ψ - realInner ψ (swapWave i j ψ) := by
    simp [pairEnergy, edgeAction, realInner_sub_right, realInner_self]
  linarith

end QMCPMatch.BlochStructural


-- Local proof source: AGMBlochPauliOps

/-! Bloch-only finite Pauli operator helpers, extracted from the checked
physical-embedding proof. No public definition is modified or redefined.
The local tables and actions are private proof auxiliaries. -/

noncomputable section
open scoped BigOperators Matrix
open QuantumMaxCutEnergy QMCPMatch.BlochFoundation
namespace QMCPMatch.BlochOps

abbrev Label := Fin 4
abbrev Word (n : ℕ) := Fin n → Label

def localProduct : Label → Label → Label :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]]

def localPhase : Label → Label → ℂ :=
  ![![1, 1, 1, 1], ![1, 1, Complex.I, -Complex.I],
    ![1, -Complex.I, 1, Complex.I], ![1, Complex.I, -Complex.I, 1]]

def identityWord (n : ℕ) : Word n := fun _ => 0



def wordProduct {n : ℕ} (P Q : Word n) : Word n :=
  fun i => localProduct (P i) (Q i)

def wordPhase {n : ℕ} (P Q : Word n) : ℂ :=
  ∏ i, localPhase (P i) (Q i)



def twoBody {n : ℕ} (a : Label) (e : Edge n) : Word n :=
  fun i => if i = e.val.1 ∨ i = e.val.2 then a else 0

def objective {n : ℕ} (w : Weights n) (L : Word n → ℝ) : ℝ :=
  ∑ e, (w e : ℝ) *
    (1 - L (twoBody 1 e) - L (twoBody 2 e) - L (twoBody 3 e)) / 2



lemma localProduct_identity_left (a : Label) : localProduct 0 a = a := by
  fin_cases a <;> decide

lemma localProduct_identity_right (a : Label) : localProduct a 0 = a := by
  fin_cases a <;> decide

lemma localProduct_eq_zero_iff (a b : Label) : localProduct a b = 0 ↔ a = b := by
  fin_cases a <;> fin_cases b <;> decide

lemma localPhase_self (a : Label) : localPhase a a = 1 := by
  fin_cases a <;> norm_num [localPhase]

lemma localPhase_identity_left (a : Label) : localPhase 0 a = 1 := by
  fin_cases a <;> norm_num [localPhase]

lemma localPhase_identity_right (a : Label) : localPhase a 0 = 1 := by
  fin_cases a <;> norm_num [localPhase]



def localFlip : Label → Bool → Bool := ![id, Bool.not, Bool.not, id]

def localAmplitude : Label → Bool → ℂ :=
  ![fun _ => 1, fun _ => 1,
    fun b => if b then Complex.I else -Complex.I,
    fun b => if b then -1 else 1]

@[simp] theorem localFlip_identity (b : Bool) : localFlip 0 b = b := by
  simp [localFlip]

@[simp] theorem localAmplitude_identity (b : Bool) : localAmplitude 0 b = 1 := by
  simp [localAmplitude]

theorem localFlip_twice (a : Label) (b : Bool) :
    localFlip a (localFlip a b) = b := by
  fin_cases a <;> cases b <;> norm_num [localFlip]

theorem localFlip_product (a b : Label) (x : Bool) :
    localFlip b (localFlip a x) = localFlip (localProduct a b) x := by
  fin_cases a <;> fin_cases b <;> cases x <;>
    norm_num [localFlip, localProduct, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail]

theorem localAmplitude_product (a b : Label) (x : Bool) :
    localAmplitude a x * localAmplitude b (localFlip a x) =
      localPhase a b * localAmplitude (localProduct a b) x := by
  fin_cases a <;> fin_cases b <;> cases x <;>
    norm_num [localAmplitude, localFlip, localProduct, localPhase,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

theorem localAmplitude_conj (a : Label) (x : Bool) :
    star (localAmplitude a x) = localAmplitude a (localFlip a x) := by
  fin_cases a <;> cases x <;> norm_num [localAmplitude, localFlip]

def shiftedBasis {n : ℕ} (P : Word n) (x : Basis n) : Basis n :=
  fun i => localFlip (P i) (x i)

def wordAmplitude {n : ℕ} (P : Word n) (x : Basis n) : ℂ :=
  ∏ i, localAmplitude (P i) (x i)

def wordAction {n : ℕ} (P : Word n) (ψ : Wave n) : Wave n :=
  fun x => wordAmplitude P x * ψ (shiftedBasis P x)

@[simp] theorem shiftedBasis_twice {n : ℕ} (P : Word n) (x : Basis n) :
    shiftedBasis P (shiftedBasis P x) = x := by
  funext i
  exact localFlip_twice (P i) (x i)

theorem shiftedBasis_product {n : ℕ} (P Q : Word n) (x : Basis n) :
    shiftedBasis Q (shiftedBasis P x) = shiftedBasis (wordProduct P Q) x := by
  funext i
  exact localFlip_product (P i) (Q i) (x i)

theorem wordAmplitude_product {n : ℕ} (P Q : Word n) (x : Basis n) :
    wordAmplitude P x * wordAmplitude Q (shiftedBasis P x) =
      wordPhase P Q * wordAmplitude (wordProduct P Q) x := by
  unfold wordAmplitude wordPhase
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact localAmplitude_product (P i) (Q i) (x i)

theorem wordAmplitude_conj {n : ℕ} (P : Word n) (x : Basis n) :
    star (wordAmplitude P x) = wordAmplitude P (shiftedBasis P x) := by
  simp only [wordAmplitude, star_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact localAmplitude_conj (P i) (x i)

theorem wordAction_product {n : ℕ} (P Q : Word n) (ψ : Wave n) :
    wordAction P (wordAction Q ψ) =
      fun x => wordPhase P Q * wordAction (wordProduct P Q) ψ x := by
  funext x
  simp only [wordAction, ← mul_assoc, wordAmplitude_product, shiftedBasis_product]

def complexInner {n : ℕ} (ψ φ : Wave n) : ℂ := ∑ x, star (ψ x) * φ x

theorem complexInner_conj {n : ℕ} (ψ φ : Wave n) :
    star (complexInner ψ φ) = complexInner φ ψ := by
  simp only [complexInner, star_sum, star_mul, star_star]

theorem complexInner_re {n : ℕ} (ψ φ : Wave n) :
    (complexInner ψ φ).re = realInner ψ φ := by
  simp only [complexInner, realInner, Complex.re_sum, Complex.mul_re,
    Complex.star_def, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add]

theorem complexInner_self {n : ℕ} (ψ : Wave n) :
    complexInner ψ ψ = (squaredNorm ψ : ℂ) := by
  simp only [complexInner, squaredNorm, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro x _
  simpa only [Complex.star_def] using (Complex.normSq_eq_conj_mul_self (z := ψ x)).symm

theorem complexInner_word_adjoint {n : ℕ} (P : Word n) (ψ φ : Wave n) :
    complexInner (wordAction P ψ) φ = complexInner ψ (wordAction P φ) := by
  calc
    complexInner (wordAction P ψ) φ =
        ∑ x, star (ψ (shiftedBasis P x)) * wordAction P φ (shiftedBasis P x) := by
      unfold complexInner
      apply Finset.sum_congr rfl
      intro x _
      simp only [wordAction, star_mul, wordAmplitude_conj, shiftedBasis_twice]
      ring
    _ = _ := (show Function.Involutive (shiftedBasis P) from shiftedBasis_twice P).bijective.sum_comp
      (fun x => star (ψ x) * wordAction P φ x)

theorem word_expectation_real {n : ℕ} (P : Word n) (ψ : Wave n) :
    (complexInner ψ (wordAction P ψ)).im = 0 := by
  have h := complexInner_conj ψ (wordAction P ψ)
  rw [complexInner_word_adjoint] at h
  have hi := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

theorem complexInner_scalar_right {n : ℕ} (ψ φ : Wave n) (c : ℂ) :
    complexInner ψ (fun x => c * φ x) = c * complexInner ψ φ := by
  unfold complexInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

@[simp] theorem wordAction_identity {n : ℕ} (ψ : Wave n) :
    wordAction (identityWord n) ψ = ψ := by
  funext x
  have hs : shiftedBasis (identityWord n) x = x := by
    funext i
    simp [shiftedBasis, identityWord]
  simp [wordAction, wordAmplitude, identityWord, hs]

def stateMoments {n : ℕ} (ψ : Wave n) (P : Word n) : ℝ :=
  (complexInner ψ (wordAction P ψ)).re

theorem stateMoments_identity {n : ℕ} (ψ : Wave n) (hψ : squaredNorm ψ = 1) :
    stateMoments ψ (identityWord n) = 1 := by
  simp [stateMoments, complexInner_self, hψ]



@[simp] theorem localFlip_one (b : Bool) : localFlip 1 b = !b := rfl
@[simp] theorem localFlip_two (b : Bool) : localFlip 2 b = !b := rfl
@[simp] theorem localFlip_three (b : Bool) : localFlip 3 b = b := rfl
@[simp] theorem localAmplitude_one (b : Bool) : localAmplitude 1 b = 1 := rfl
@[simp] theorem localAmplitude_two (b : Bool) :
    localAmplitude 2 b = if b then Complex.I else -Complex.I := rfl
@[simp] theorem localAmplitude_three (b : Bool) :
    localAmplitude 3 b = if b then -1 else 1 := rfl

def singleWord {n : ℕ} (a : Label) (i : Fin n) : Word n :=
  fun j => if j = i then a else 0

theorem wordAmplitude_single {n : ℕ} (a : Label) (i : Fin n) (x : Basis n) :
    wordAmplitude (singleWord a i) x = localAmplitude a (x i) := by
  classical
  have hf (j : Fin n) : localAmplitude (singleWord a i j) (x j) =
      if j = i then localAmplitude a (x j) else 1 := by
    by_cases h : j = i <;> simp [singleWord, h]
  simp only [wordAmplitude, hf]
  simp

theorem shiftedBasis_single {n : ℕ} (a : Label) (i : Fin n) (x : Basis n) :
    shiftedBasis (singleWord a i) x = Function.update x i (localFlip a (x i)) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [shiftedBasis, singleWord]
  · simp [shiftedBasis, singleWord, h]

theorem wordAction_single_X {n : ℕ} (i : Fin n) (ψ : Wave n) :
    wordAction (singleWord 1 i) ψ = BlochStructural.pauliX i ψ := by
  funext x
  simp [wordAction, wordAmplitude_single, shiftedBasis_single, BlochStructural.pauliX, flipBit]

theorem wordAction_single_Y {n : ℕ} (i : Fin n) (ψ : Wave n) :
    wordAction (singleWord 2 i) ψ = BlochStructural.pauliY i ψ := by
  funext x
  cases h : x i <;>
    simp [wordAction, wordAmplitude_single, shiftedBasis_single, BlochStructural.pauliY, flipBit, h]

theorem wordAction_single_Z {n : ℕ} (i : Fin n) (ψ : Wave n) :
    wordAction (singleWord 3 i) ψ = BlochStructural.pauliZ i ψ := by
  funext x
  simp only [wordAction, wordAmplitude_single, shiftedBasis_single,
    localFlip_three, Function.update_eq_self]
  cases h : x i <;> simp [BlochStructural.pauliZ, h]

theorem singleWord_product {n : ℕ} (a : Label) (e : Edge n) :
    wordProduct (singleWord a e.val.1) (singleWord a e.val.2) = twoBody a e := by
  have hij : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  funext j
  by_cases hi : j = e.val.1
  · subst j
    simp [wordProduct, singleWord, twoBody, hij, localProduct_identity_right]
  · by_cases hj : j = e.val.2
    · subst j
      simp [wordProduct, singleWord, twoBody, Ne.symm hij, localProduct_identity_left]
    · simp [wordProduct, singleWord, twoBody, hi, hj, localProduct_identity_left]

theorem singleWord_phase {n : ℕ} (a : Label) (e : Edge n) :
    wordPhase (singleWord a e.val.1) (singleWord a e.val.2) = 1 := by
  have hij : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  apply Finset.prod_eq_one
  intro j _
  by_cases hi : j = e.val.1
  · subst j
    simp [singleWord, hij, localPhase_identity_right]
  · by_cases hj : j = e.val.2
    · subst j
      simp [singleWord, Ne.symm hij, localPhase_identity_left]
    · simp [singleWord, hi, hj, localPhase_identity_left]

theorem wordAction_twoBody {n : ℕ} (a : Label) (e : Edge n) (ψ : Wave n) :
    wordAction (twoBody a e) ψ =
      wordAction (singleWord a e.val.1) (wordAction (singleWord a e.val.2) ψ) := by
  have h := wordAction_product (singleWord a e.val.1) (singleWord a e.val.2) ψ
  rw [singleWord_product, singleWord_phase] at h
  simpa only [one_mul] using h.symm

theorem stateMoments_twoBody_X {n : ℕ} (ψ : Wave n) (e : Edge n) :
    stateMoments ψ (twoBody 1 e) =
      realInner (BlochStructural.pauliX e.val.1 ψ) (BlochStructural.pauliX e.val.2 ψ) := by
  rw [stateMoments, wordAction_twoBody, wordAction_single_X, wordAction_single_X,
    complexInner_re, ← BlochStructural.pauliX_adjoint]

theorem stateMoments_twoBody_Y {n : ℕ} (ψ : Wave n) (e : Edge n) :
    stateMoments ψ (twoBody 2 e) =
      realInner (BlochStructural.pauliY e.val.1 ψ) (BlochStructural.pauliY e.val.2 ψ) := by
  rw [stateMoments, wordAction_twoBody, wordAction_single_Y, wordAction_single_Y,
    complexInner_re, ← BlochStructural.pauliY_adjoint]

theorem stateMoments_twoBody_Z {n : ℕ} (ψ : Wave n) (e : Edge n) :
    stateMoments ψ (twoBody 3 e) =
      realInner (BlochStructural.pauliZ e.val.1 ψ) (BlochStructural.pauliZ e.val.2 ψ) := by
  rw [stateMoments, wordAction_twoBody, wordAction_single_Z, wordAction_single_Z,
    complexInner_re, ← BlochStructural.pauliZ_adjoint]

theorem stateMoments_objective {n : ℕ} (w : Weights n) (ψ : Wave n)
    (hψ : squaredNorm ψ = 1) :
    objective w (stateMoments ψ) = energy w ψ := by
  rw [objective, energy_eq_pairEnergy]
  apply Finset.sum_congr rfl
  intro e _
  have hentry := BlochStructural.pauli_correlation_sum ψ e.val.1 e.val.2 (ne_of_lt e.property)
  rw [hψ] at hentry
  rw [stateMoments_twoBody_X, stateMoments_twoBody_Y, stateMoments_twoBody_Z]
  have hlocal : 1 - realInner (BlochStructural.pauliX e.val.1 ψ) (BlochStructural.pauliX e.val.2 ψ) -
      realInner (BlochStructural.pauliY e.val.1 ψ) (BlochStructural.pauliY e.val.2 ψ) -
      realInner (BlochStructural.pauliZ e.val.1 ψ) (BlochStructural.pauliZ e.val.2 ψ) =
      2 * pairEnergy e.val.1 e.val.2 ψ := by linarith
  rw [hlocal]
  ring



end QMCPMatch.BlochOps


-- Local proof source: AGMBlochTensorCore

/-!
Actual pure product-state witnesses for rank-three Bloch vectors.
Sources: GP19 Bloch-vector representation and product energy formula;
AGM20 Eq. (6). This is an analytic existence proof, not state preparation.
-/

noncomputable section
open scoped BigOperators Matrix
open QuantumMaxCutEnergy QMCPMatch.BlochFoundation
open QMCPMatch.BlochOps
open QMCPMatch.BlochOps

namespace QMCPMatch.Bloch

def localExpectation (φ : Bool → ℂ) (a : Label) : ℂ :=
  ∑ b : Bool, star (φ b) * localAmplitude a b * φ (localFlip a b)

def productWave {n : ℕ} (φ : Fin n → Bool → ℂ) : Wave n :=
  fun x => ∏ i, φ i (x i)

theorem productWave_norm {n : ℕ} (φ : Fin n → Bool → ℂ)
    (hφ : ∀ i, Complex.normSq (φ i false) + Complex.normSq (φ i true) = 1) :
    squaredNorm (productWave φ) = 1 := by
  simp only [squaredNorm, productWave, map_prod]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) => Complex.normSq (φ i b))]
  have hs (i : Fin n) : (∑ b : Bool, Complex.normSq (φ i b)) = 1 := by
    simpa [Fintype.sum_bool, add_comm] using hφ i
  apply Finset.prod_eq_one
  intro i _
  exact hs i

theorem productWave_word_expectation {n : ℕ} (φ : Fin n → Bool → ℂ) (P : Word n) :
    complexInner (productWave φ) (wordAction P (productWave φ)) =
      ∏ i, localExpectation (φ i) (P i) := by
  unfold complexInner wordAction productWave wordAmplitude shiftedBasis localExpectation
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [star_prod]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

theorem localExpectation_identity (φ : Bool → ℂ)
    (hφ : Complex.normSq (φ false) + Complex.normSq (φ true) = 1) :
    localExpectation φ 0 = 1 := by
  simp only [localExpectation, localAmplitude_identity, localFlip_identity, mul_one]
  have hm (b : Bool) : star (φ b) * φ b = (Complex.normSq (φ b) : ℂ) := by
    simpa only [Complex.star_def] using (Complex.normSq_eq_conj_mul_self (z := φ b)).symm
  simp_rw [hm]
  rw [← Complex.ofReal_sum]
  have hs : (∑ b : Bool, Complex.normSq (φ b)) = 1 := by
    simpa [Fintype.sum_bool, add_comm] using hφ
  rw [hs]
  rfl

def qubit (a u v : ℝ) : Bool → ℂ := fun b => if b then ⟨u, v⟩ else (a : ℂ)

theorem qubit_norm (a u v : ℝ) :
    Complex.normSq (qubit a u v false) + Complex.normSq (qubit a u v true) =
      a ^ 2 + u ^ 2 + v ^ 2 := by
  simp [qubit, Complex.normSq_apply]
  ring

theorem qubit_X (a u v : ℝ) :
    localExpectation (qubit a u v) 1 = ((2 * a * u : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [localExpectation, Fintype.sum_bool, qubit, Complex.star_def,
      Complex.mul_re, Complex.mul_im, pow_two] <;> ring

theorem qubit_Y (a u v : ℝ) :
    localExpectation (qubit a u v) 2 = ((2 * a * v : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [localExpectation, Fintype.sum_bool, qubit, Complex.star_def,
      Complex.mul_re, Complex.mul_im, pow_two] <;> ring

theorem qubit_Z (a u v : ℝ) :
    localExpectation (qubit a u v) 3 = ((a ^ 2 - u ^ 2 - v ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [localExpectation, Fintype.sum_bool, qubit, Complex.star_def,
      Complex.mul_re, Complex.mul_im, pow_two] <;> ring


end QMCPMatch.Bloch


-- Local proof source: AGMBlochProductState

noncomputable section
open scoped BigOperators Matrix
open QuantumMaxCutEnergy QMCPMatch.BlochFoundation
open QMCPMatch.BlochOps
namespace QMCPMatch.Bloch

theorem qubit_of_unit_bloch (x y z : ℝ) (hunit : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    ∃ φ : Bool → ℂ,
      Complex.normSq (φ false) + Complex.normSq (φ true) = 1 ∧
      localExpectation φ 1 = (x : ℂ) ∧ localExpectation φ 2 = (y : ℂ) ∧
      localExpectation φ 3 = (z : ℂ) := by
  by_cases hz : z = -1
  · subst z
    have hx2 : x ^ 2 = 0 := by nlinarith only [hunit, sq_nonneg y]
    have hy2 : y ^ 2 = 0 := by nlinarith only [hunit, sq_nonneg x]
    have hx : x = 0 := sq_eq_zero_iff.mp hx2
    have hy : y = 0 := sq_eq_zero_iff.mp hy2
    refine ⟨qubit 0 1 0, ?_, ?_, ?_, ?_⟩ <;>
      simp [qubit_norm, qubit_X, qubit_Y, qubit_Z, hx, hy]
  · have hzlower : -1 ≤ z := by
      nlinarith only [hunit, sq_nonneg x, sq_nonneg y, sq_nonneg (z + 1)]
    have hzstrict : -1 < z := lt_of_le_of_ne hzlower (Ne.symm hz)
    have hpos : 0 < (1 + z) / 2 := by linarith
    let a := Real.sqrt ((1 + z) / 2)
    have ha : 0 < a := Real.sqrt_pos.mpr hpos
    have ha2 : a ^ 2 = (1 + z) / 2 := Real.sq_sqrt hpos.le
    have hxy : x ^ 2 + y ^ 2 = (1 - z) * (1 + z) := by nlinarith only [hunit]
    have hden : (2 * a) ^ 2 = 2 * (1 + z) := by nlinarith only [ha2]
    have hz1 : 1 + z ≠ 0 := by linarith only [hzstrict]
    have huv : (x / (2 * a)) ^ 2 + (y / (2 * a)) ^ 2 = (1 - z) / 2 := by
      rw [div_pow, div_pow, ← add_div, hxy, hden]
      field_simp [hz1]
    have hx : 2 * a * (x / (2 * a)) = x := by field_simp [ne_of_gt ha]
    have hy : 2 * a * (y / (2 * a)) = y := by field_simp [ne_of_gt ha]
    refine ⟨qubit a (x / (2 * a)) (y / (2 * a)), ?_, ?_, ?_, ?_⟩
    · rw [qubit_norm]
      linarith only [ha2, huv]
    · rw [qubit_X, hx]
    · rw [qubit_Y, hy]
    · rw [qubit_Z]
      congr 1
      linarith only [ha2, huv]


end QMCPMatch.Bloch

-- Partially entangled matching states (ALMPS25, Lemma 5 / Algorithm 2)

noncomputable section
open scoped BigOperators
open QuantumMaxCutEnergy QMCPMatch.BlochFoundation QMCPMatch.BlochStructural
  QMCPMatch.BlochOps QMCPMatch.Bloch

namespace QMCPMatch

/-! ### Normalised expectation over the computational basis, and independence -/

def cardC (n : ℕ) : ℂ := ((Fintype.card (Basis n) : ℕ) : ℂ)

def Nr (n : ℕ) : ℝ := ((Fintype.card (Basis n) : ℕ) : ℝ)

lemma Nr_pos (n : ℕ) : 0 < Nr n := by
  unfold Nr
  exact_mod_cast Fintype.card_pos

lemma cardC_ne_zero (n : ℕ) : cardC n ≠ 0 := by
  unfold cardC
  exact_mod_cast Fintype.card_ne_zero

lemma Nr_cast (n : ℕ) : ((Nr n : ℝ) : ℂ) = cardC n :=
  Complex.ofReal_natCast _

def E {n : ℕ} (F : Basis n → ℂ) : ℂ := (∑ x, F x) / cardC n

lemma sum_eq_E {n : ℕ} (F : Basis n → ℂ) : ∑ x, F x = cardC n * E F := by
  have h := cardC_ne_zero n
  unfold E
  field_simp

lemma E_const_one {n : ℕ} : E (fun _ : Basis n => (1 : ℂ)) = 1 := by
  unfold E
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact div_self (cardC_ne_zero n)

def DepOn {n : ℕ} (F : Basis n → ℂ) (S : Finset (Fin n)) : Prop :=
  ∀ x y : Basis n, (∀ k ∈ S, x k = y k) → F x = F y

def mix {n : ℕ} (S : Finset (Fin n)) (x y : Basis n) : Basis n :=
  fun k => if k ∈ S then x k else y k

lemma sum_mix {n : ℕ} (S : Finset (Fin n)) (H : Basis n → ℂ) :
    ∑ x : Basis n, ∑ y : Basis n, H (mix S x y) = cardC n * ∑ z, H z := by
  classical
  let e : Basis n × Basis n → Basis n × Basis n :=
    fun p => (mix S p.1 p.2, mix S p.2 p.1)
  have he : Function.Involutive e := by
    intro p
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
      by_cases hk : k ∈ S <;> simp [e, mix, hk]
  have h1 : ∑ p : Basis n × Basis n, H (mix S p.1 p.2) = ∑ p : Basis n × Basis n, H p.1 :=
    he.bijective.sum_comp (fun p : Basis n × Basis n => H p.1)
  calc ∑ x : Basis n, ∑ y : Basis n, H (mix S x y)
      = ∑ p : Basis n × Basis n, H (mix S p.1 p.2) :=
        (Fintype.sum_prod_type' (fun x y : Basis n => H (mix S x y))).symm
    _ = ∑ p : Basis n × Basis n, H p.1 := h1
    _ = ∑ x : Basis n, ∑ _y : Basis n, H x :=
        Fintype.sum_prod_type' (fun (x : Basis n) (_ : Basis n) => H x)
    _ = cardC n * ∑ z, H z := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rfl

lemma E_mul_indep {n : ℕ} {S T : Finset (Fin n)} {F G : Basis n → ℂ}
    (hF : DepOn F S) (hG : DepOn G T) (hST : Disjoint S T) :
    E (fun x => F x * G x) = E F * E G := by
  classical
  have h : ∑ x : Basis n, ∑ y : Basis n, F (mix S x y) * G (mix S x y) =
      cardC n * ∑ z, F z * G z := sum_mix S (fun z => F z * G z)
  have h2 : ∑ x : Basis n, ∑ y : Basis n, F (mix S x y) * G (mix S x y) =
      (∑ x, F x) * ∑ y, G y := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [hF (mix S x y) x (fun k hk => by simp [mix, hk]),
      hG (mix S x y) y (fun k hk => by
        have hkS : k ∉ S := fun hS => (Finset.disjoint_left.mp hST hS) hk
        simp [mix, hkS])]
  have h3 := h2.symm.trans h
  have hc := cardC_ne_zero n
  unfold E
  rw [div_mul_div_comm, h3, mul_div_mul_left _ _ hc]

lemma DepOn_prod {n : ℕ} {ι : Type} (T : Finset ι) (S : ι → Finset (Fin n))
    (H : ι → Basis n → ℂ) [DecidableEq ι]
    (hd : ∀ c ∈ T, DepOn (H c) (S c)) :
    DepOn (fun x => ∏ c ∈ T, H c x) (T.biUnion S) := by
  intro x y hxy
  exact Finset.prod_congr rfl fun c hc =>
    hd c hc x y fun k hk => hxy k (Finset.mem_biUnion.mpr ⟨c, hc, hk⟩)

lemma E_prod {n : ℕ} {ι : Type} [DecidableEq ι] (T : Finset ι) (S : ι → Finset (Fin n))
    (H : ι → Basis n → ℂ)
    (hd : ∀ c ∈ T, DepOn (H c) (S c))
    (hdisj : ∀ c ∈ T, ∀ c' ∈ T, c ≠ c' → Disjoint (S c) (S c')) :
    E (fun x => ∏ c ∈ T, H c x) = ∏ c ∈ T, E (H c) := by
  induction T using Finset.induction_on with
  | empty => simpa using (E_const_one (n := n))
  | @insert a T ha ih =>
    have hdT : ∀ c ∈ T, DepOn (H c) (S c) := fun c hc => hd c (Finset.mem_insert_of_mem hc)
    have hdisjT : ∀ c ∈ T, ∀ c' ∈ T, c ≠ c' → Disjoint (S c) (S c') :=
      fun c hc c' hc' => hdisj c (Finset.mem_insert_of_mem hc) c' (Finset.mem_insert_of_mem hc')
    have hdj : Disjoint (S a) (T.biUnion S) := by
      rw [Finset.disjoint_biUnion_right]
      intro c hc
      exact hdisj a (Finset.mem_insert_self a T) c (Finset.mem_insert_of_mem hc)
        (by rintro rfl; exact ha hc)
    have hstep : E (fun x => H a x * ∏ c ∈ T, H c x) = E (H a) * E (fun x => ∏ c ∈ T, H c x) :=
      E_mul_indep (hd a (Finset.mem_insert_self a T)) (DepOn_prod T S H hdT) hdj
    simp only [Finset.prod_insert ha]
    rw [hstep, ih hdT hdisjT]

/-! ### Block-product waves -/

def blockWave {n : ℕ} {ι : Type} (T : Finset ι) (F : ι → Basis n → ℂ) : Wave n :=
  fun x => ∏ c ∈ T, F c x

lemma blockWave_inner {n : ℕ} {ι : Type} [DecidableEq ι] (T : Finset ι)
    (S : ι → Finset (Fin n)) (F F' : ι → Basis n → ℂ)
    (hd : ∀ c ∈ T, DepOn (F c) (S c)) (hd' : ∀ c ∈ T, DepOn (F' c) (S c))
    (hdisj : ∀ c ∈ T, ∀ c' ∈ T, c ≠ c' → Disjoint (S c) (S c')) :
    complexInner (blockWave T F) (blockWave T F') =
      cardC n * ∏ c ∈ T, E (fun x => star (F c x) * F' c x) := by
  have hdd : ∀ c ∈ T, DepOn (fun x => star (F c x) * F' c x) (S c) := by
    intro c hc x y h
    show star (F c x) * F' c x = star (F c y) * F' c y
    rw [hd c hc x y h, hd' c hc x y h]
  have key : E (fun x => ∏ c ∈ T, star (F c x) * F' c x) =
      ∏ c ∈ T, E (fun x => star (F c x) * F' c x) :=
    E_prod T S (fun c x => star (F c x) * F' c x) hdd hdisj
  rw [← key, ← sum_eq_E]
  unfold complexInner blockWave
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [star_prod, Finset.prod_mul_distrib]

lemma blockWave_op {n : ℕ} {ι : Type} [DecidableEq ι] (T : Finset ι)
    (S : ι → Finset (Fin n)) (F : ι → Basis n → ℂ)
    (hd : ∀ c ∈ T, DepOn (F c) (S c))
    (hdisj : ∀ c ∈ T, ∀ c' ∈ T, c ≠ c' → Disjoint (S c) (S c'))
    {b : ι} (hb : b ∈ T) (m : Basis n → ℂ) (τ : Basis n → Basis n)
    (hτ : ∀ x k, k ∉ S b → τ x k = x k) :
    (fun x => m x * blockWave T F (τ x)) =
      blockWave T (Function.update F b (fun x => m x * F b (τ x))) := by
  funext x
  show m x * ∏ c ∈ T, F c (τ x) =
    ∏ c ∈ T, Function.update F b (fun x => m x * F b (τ x)) c x
  have hrest : ∏ c ∈ T.erase b, Function.update F b (fun x => m x * F b (τ x)) c x =
      ∏ c ∈ T.erase b, F c (τ x) := by
    refine Finset.prod_congr rfl fun c hc => ?_
    have hcb : c ≠ b := Finset.ne_of_mem_erase hc
    have hcT : c ∈ T := Finset.mem_of_mem_erase hc
    rw [Function.update_of_ne hcb]
    exact (hd c hcT _ _ fun k hk =>
      hτ x k (fun hkb => Finset.disjoint_left.mp (hdisj c hcT b hb hcb) hk hkb)).symm
  rw [← Finset.mul_prod_erase T (fun c => F c (τ x)) hb,
    ← Finset.mul_prod_erase T
      (fun c => Function.update F b (fun x => m x * F b (τ x)) c x) hb, hrest]
  simp only [Function.update_self]
  rw [mul_assoc]

lemma dep_update {n : ℕ} {ι : Type} [DecidableEq ι] {T : Finset ι}
    {S : ι → Finset (Fin n)} {F : ι → Basis n → ℂ}
    (hd : ∀ c ∈ T, DepOn (F c) (S c)) {b : ι} {G : Basis n → ℂ} (hG : DepOn G (S b)) :
    ∀ c ∈ T, DepOn (Function.update F b G c) (S c) := by
  intro c hc
  by_cases h : c = b
  · subst h
    rw [Function.update_self]
    exact hG
  · rw [Function.update_of_ne h]
    exact hd c hc

lemma prod_E_update {n : ℕ} {ι : Type} [DecidableEq ι] {T : Finset ι}
    {F : ι → Basis n → ℂ}
    (hnorm : ∀ c ∈ T, E (fun x => star (F c x) * F c x) = 1)
    {b : ι} (hb : b ∈ T) (G : Basis n → ℂ) :
    ∏ c ∈ T, E (fun x => star (F c x) * Function.update F b G c x) =
      E (fun x => star (F b x) * G x) := by
  rw [← Finset.mul_prod_erase T
    (fun c => E (fun x => star (F c x) * Function.update F b G c x)) hb]
  simp only [Function.update_self]
  rw [Finset.prod_eq_one, mul_one]
  intro c hc
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hc)]
  exact hnorm c (Finset.mem_of_mem_erase hc)

lemma prod_E_update2 {n : ℕ} {ι : Type} [DecidableEq ι] {T : Finset ι}
    {F : ι → Basis n → ℂ}
    (hnorm : ∀ c ∈ T, E (fun x => star (F c x) * F c x) = 1)
    {b b' : ι} (hb : b ∈ T) (hb' : b' ∈ T) (hne : b ≠ b') (Gi Gj : Basis n → ℂ) :
    ∏ c ∈ T, E (fun x => star (F c x) *
        Function.update (Function.update F b' Gj) b Gi c x) =
      E (fun x => star (F b x) * Gi x) * E (fun x => star (F b' x) * Gj x) := by
  have hb'' : b' ∈ T.erase b := Finset.mem_erase.mpr ⟨hne.symm, hb'⟩
  rw [← Finset.mul_prod_erase T
    (fun c => E (fun x => star (F c x) *
      Function.update (Function.update F b' Gj) b Gi c x)) hb,
    ← Finset.mul_prod_erase (T.erase b)
    (fun c => E (fun x => star (F c x) *
      Function.update (Function.update F b' Gj) b Gi c x)) hb'']
  simp only [Function.update_self, Function.update_of_ne hne.symm]
  rw [Finset.prod_eq_one, mul_one]
  intro c hc
  have h1 : c ≠ b' := Finset.ne_of_mem_erase hc
  have hc2 : c ∈ T.erase b := Finset.mem_of_mem_erase hc
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hc2), Function.update_of_ne h1]
  exact hnorm c (Finset.mem_of_mem_erase hc2)

/-- One-site Pauli action in explicit form. -/
def sOp {n : ℕ} (a : Label) (i : Fin n) (ψ : Wave n) : Wave n :=
  fun x => localAmplitude a (x i) * ψ (Function.update x i (localFlip a (x i)))

lemma wordAction_single {n : ℕ} (a : Label) (i : Fin n) (ψ : Wave n) :
    wordAction (singleWord a i) ψ = sOp a i ψ := by
  funext x
  simp only [wordAction, wordAmplitude_single, shiftedBasis_single, sOp]

lemma sOp_dep {n : ℕ} {G : Basis n → ℂ} {S : Finset (Fin n)} (hG : DepOn G S)
    (a : Label) {i : Fin n} (hi : i ∈ S) : DepOn (sOp a i G) S := by
  intro x y hxy
  show localAmplitude a (x i) * G (Function.update x i (localFlip a (x i))) =
    localAmplitude a (y i) * G (Function.update y i (localFlip a (y i)))
  rw [hxy i hi]
  congr 1
  apply hG
  intro k hk
  by_cases hki : k = i
  · subst hki
    simp
  · simp [Function.update_of_ne hki, hxy k hk]

structure Sys {n : ℕ} {ι : Type} (T : Finset ι) (S : ι → Finset (Fin n))
    (F : ι → Basis n → ℂ) : Prop where
  dep : ∀ c ∈ T, DepOn (F c) (S c)
  disj : ∀ c ∈ T, ∀ c' ∈ T, c ≠ c' → Disjoint (S c) (S c')
  norm : ∀ c ∈ T, E (fun x => star (F c x) * F c x) = 1

theorem Sys.sqnorm {n : ℕ} {ι : Type} [DecidableEq ι] {T : Finset ι}
    {S : ι → Finset (Fin n)} {F : ι → Basis n → ℂ} (h : Sys T S F) :
    squaredNorm (blockWave T F) = Nr n := by
  have h1 := blockWave_inner T S F F h.dep h.dep h.disj
  rw [Finset.prod_eq_one h.norm, mul_one, complexInner_self, ← Nr_cast] at h1
  exact Complex.ofReal_injective h1

theorem Sys.swap {n : ℕ} {ι : Type} [DecidableEq ι] {T : Finset ι}
    {S : ι → Finset (Fin n)} {F : ι → Basis n → ℂ} (h : Sys T S F)
    {b : ι} (hb : b ∈ T) {i j : Fin n} (hi : i ∈ S b) (hj : j ∈ S b) :
    complexInner (blockWave T F) (swapWave i j (blockWave T F)) =
      cardC n * E (fun x => star (F b x) * (1 * F b (x ∘ Equiv.swap i j))) := by
  have hop : (fun x => (1 : ℂ) * blockWave T F (x ∘ Equiv.swap i j)) =
      blockWave T (Function.update F b (fun x => (1 : ℂ) * F b (x ∘ Equiv.swap i j))) :=
    blockWave_op T S F h.dep h.disj hb (fun _ => 1) (fun x => x ∘ Equiv.swap i j)
      (fun x k hk => by
        have h1 : k ≠ i := fun e => hk (by rw [e]; exact hi)
        have h2 : k ≠ j := fun e => hk (by rw [e]; exact hj)
        simp [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2])
  have hG : DepOn (fun x => (1 : ℂ) * F b (x ∘ Equiv.swap i j)) (S b) := by
    intro x y hxy
    have hxy' : F b (x ∘ Equiv.swap i j) = F b (y ∘ Equiv.swap i j) := by
      apply h.dep b hb
      intro k hk
      simp only [Function.comp_apply]
      apply hxy
      by_cases h1 : k = i
      · subst h1
        rw [Equiv.swap_apply_left]
        exact hj
      · by_cases h2 : k = j
        · subst h2
          rw [Equiv.swap_apply_right]
          exact hi
        · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
          exact hk
    show (1 : ℂ) * F b (x ∘ Equiv.swap i j) = (1 : ℂ) * F b (y ∘ Equiv.swap i j)
    rw [hxy']
  have hsw : swapWave i j (blockWave T F) =
      fun x => (1 : ℂ) * blockWave T F (x ∘ Equiv.swap i j) := by
    funext x
    simp [swapWave]
  rw [hsw, hop, blockWave_inner T S F _ h.dep (dep_update h.dep hG) h.disj,
    prod_E_update h.norm hb]

theorem Sys.cross {n : ℕ} {ι : Type} [DecidableEq ι] {T : Finset ι}
    {S : ι → Finset (Fin n)} {F : ι → Basis n → ℂ} (h : Sys T S F)
    {b b' : ι} (hb : b ∈ T) (hb' : b' ∈ T) (hne : b ≠ b')
    {i j : Fin n} (hi : i ∈ S b) (hj : j ∈ S b') (a a' : Label) :
    complexInner (blockWave T F) (sOp a i (sOp a' j (blockWave T F))) =
      cardC n * (E (fun x => star (F b x) * sOp a i (F b) x) *
        E (fun x => star (F b' x) * sOp a' j (F b') x)) := by
  have hτ : ∀ (b : ι) (i : Fin n) (a : Label), i ∈ S b → ∀ (x : Basis n) (k : Fin n),
      k ∉ S b → Function.update x i (localFlip a (x i)) k = x k := by
    intro b i a hi x k hk
    exact Function.update_of_ne (fun e => hk (by rw [e]; exact hi)) _ _
  have h1 : sOp a' j (blockWave T F) =
      blockWave T (Function.update F b' (sOp a' j (F b'))) :=
    blockWave_op T S F h.dep h.disj hb' (fun x => localAmplitude a' (x j))
      (fun x => Function.update x j (localFlip a' (x j))) (hτ b' j a' hj)
  have hd1 : ∀ c ∈ T, DepOn (Function.update F b' (sOp a' j (F b')) c) (S c) :=
    dep_update h.dep (sOp_dep (h.dep b' hb') a' hj)
  have h2 : sOp a i (blockWave T (Function.update F b' (sOp a' j (F b')))) =
      blockWave T (Function.update (Function.update F b' (sOp a' j (F b'))) b
        (sOp a i (F b))) := by
    have h3 : sOp a i (blockWave T (Function.update F b' (sOp a' j (F b')))) =
        blockWave T (Function.update (Function.update F b' (sOp a' j (F b'))) b
          (sOp a i (Function.update F b' (sOp a' j (F b')) b))) :=
      blockWave_op T S (Function.update F b' (sOp a' j (F b'))) hd1 h.disj hb
        (fun x => localAmplitude a (x i))
        (fun x => Function.update x i (localFlip a (x i))) (hτ b i a hi)
    rw [Function.update_of_ne hne] at h3
    exact h3
  have hd2 : ∀ c ∈ T, DepOn (Function.update (Function.update F b' (sOp a' j (F b'))) b
      (sOp a i (F b)) c) (S c) :=
    dep_update hd1 (sOp_dep (h.dep b hb) a hi)
  rw [h1, h2, blockWave_inner T S F _ h.dep hd2 h.disj, prod_E_update2 h.norm hb hb' hne]

lemma pauliX_inner {n : ℕ} (ψ : Wave n) (i j : Fin n) :
    realInner (pauliX i ψ) (pauliX j ψ) = (complexInner ψ (sOp 1 i (sOp 1 j ψ))).re := by
  rw [← wordAction_single, ← wordAction_single, ← complexInner_word_adjoint, complexInner_re,
    wordAction_single_X, wordAction_single_X]

lemma pauliY_inner {n : ℕ} (ψ : Wave n) (i j : Fin n) :
    realInner (pauliY i ψ) (pauliY j ψ) = (complexInner ψ (sOp 2 i (sOp 2 j ψ))).re := by
  rw [← wordAction_single, ← wordAction_single, ← complexInner_word_adjoint, complexInner_re,
    wordAction_single_Y, wordAction_single_Y]

lemma pauliZ_inner {n : ℕ} (ψ : Wave n) (i j : Fin n) :
    realInner (pauliZ i ψ) (pauliZ j ψ) = (complexInner ψ (sOp 3 i (sOp 3 j ψ))).re := by
  rw [← wordAction_single, ← wordAction_single, ← complexInner_word_adjoint, complexInner_re,
    wordAction_single_Z, wordAction_single_Z]

theorem Sys.pairEnergy_cross {n : ℕ} {ι : Type} [DecidableEq ι] {T : Finset ι}
    {S : ι → Finset (Fin n)} {F : ι → Basis n → ℂ} (h : Sys T S F)
    {b b' : ι} (hb : b ∈ T) (hb' : b' ∈ T) (hne : b ≠ b')
    {i j : Fin n} (hi : i ∈ S b) (hj : j ∈ S b') (hij : i ≠ j)
    (m1 m2 m3 m1' m2' m3' : ℝ)
    (h1 : E (fun x => star (F b x) * sOp 1 i (F b) x) = (m1 : ℂ))
    (h2 : E (fun x => star (F b x) * sOp 2 i (F b) x) = (m2 : ℂ))
    (h3 : E (fun x => star (F b x) * sOp 3 i (F b) x) = (m3 : ℂ))
    (h1' : E (fun x => star (F b' x) * sOp 1 j (F b') x) = (m1' : ℂ))
    (h2' : E (fun x => star (F b' x) * sOp 2 j (F b') x) = (m2' : ℂ))
    (h3' : E (fun x => star (F b' x) * sOp 3 j (F b') x) = (m3' : ℂ)) :
    pairEnergy i j (blockWave T F) =
      Nr n * ((1 - (m1 * m1' + m2 * m2' + m3 * m3')) / 2) := by
  have k1 : (complexInner (blockWave T F) (sOp 1 i (sOp 1 j (blockWave T F)))).re =
      Nr n * (m1 * m1') := by
    rw [h.cross hb hb' hne hi hj 1 1, h1, h1', ← Nr_cast, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have k2 : (complexInner (blockWave T F) (sOp 2 i (sOp 2 j (blockWave T F)))).re =
      Nr n * (m2 * m2') := by
    rw [h.cross hb hb' hne hi hj 2 2, h2, h2', ← Nr_cast, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have k3 : (complexInner (blockWave T F) (sOp 3 i (sOp 3 j (blockWave T F)))).re =
      Nr n * (m3 * m3') := by
    rw [h.cross hb hb' hne hi hj 3 3, h3, h3', ← Nr_cast, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have hp := pauli_correlation_sum (blockWave T F) i j hij
  rw [pauliX_inner, pauliY_inner, pauliZ_inner, k1, k2, k3, h.sqnorm] at hp
  linarith

theorem Sys.pairEnergy_same {n : ℕ} {ι : Type} [DecidableEq ι] {T : Finset ι}
    {S : ι → Finset (Fin n)} {F : ι → Basis n → ℂ} (h : Sys T S F)
    {b : ι} (hb : b ∈ T) {i j : Fin n} (hi : i ∈ S b) (hj : j ∈ S b) (v : ℝ)
    (hv : E (fun x => star (F b x) * (1 * F b (x ∘ Equiv.swap i j))) = (v : ℂ)) :
    pairEnergy i j (blockWave T F) = Nr n * (1 - v) := by
  have h1 : pairEnergy i j (blockWave T F) = squaredNorm (blockWave T F) -
      (complexInner (blockWave T F) (swapWave i j (blockWave T F))).re := by
    rw [complexInner_re]
    simp [pairEnergy, edgeAction, realInner_sub_right, realInner_self]
  rw [h1, h.sqnorm, h.swap hb hi hj, hv, ← Nr_cast, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-! ### Coordinate expectations -/

lemma flip_sum {n : ℕ} (i : Fin n) (H : Basis n → ℂ) :
    ∑ x, H (flipBit i x) = ∑ x, H x :=
  (flipBit_involutive i).bijective.sum_comp H

lemma E_coord {n : ℕ} (i : Fin n) (g : Bool → ℂ) :
    E (fun x : Basis n => g (x i)) = (g false + g true) / 2 := by
  have hi : ∀ x : Basis n, flipBit i x i = !(x i) := fun x => by simp [flipBit]
  have h1 : ∑ x : Basis n, g (!(x i)) = ∑ x : Basis n, g (x i) := by
    have h := flip_sum i (fun x => g (x i))
    simpa only [hi] using h
  have h2 : ∑ x : Basis n, (g (x i) + g (!(x i))) = ∑ _x : Basis n, (g false + g true) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    cases x i <;> simp only [Bool.not_true, Bool.not_false] <;> ring
  rw [Finset.sum_add_distrib, h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
  have h3 : (∑ x : Basis n, g (x i)) + ∑ x : Basis n, g (x i) =
      cardC n * (g false + g true) := h2
  have hc := cardC_ne_zero n
  unfold E
  field_simp
  linear_combination h3

lemma E_coord2 {n : ℕ} (i j : Fin n) (hij : i ≠ j) (g : Bool → Bool → ℂ) :
    E (fun x : Basis n => g (x i) (x j)) =
      (g false false + g false true + g true false + g true true) / 4 := by
  have hi : ∀ x : Basis n, flipBit i x i = !(x i) := fun x => by simp [flipBit]
  have hj : ∀ x : Basis n, flipBit j x j = !(x j) := fun x => by simp [flipBit]
  have hij' : ∀ x : Basis n, flipBit i x j = x j := fun x => by
    simp [flipBit, Function.update_of_ne (Ne.symm hij)]
  have hji' : ∀ x : Basis n, flipBit j x i = x i := fun x => by
    simp [flipBit, Function.update_of_ne hij]
  have h1 : ∑ x : Basis n, g (!(x i)) (x j) = ∑ x : Basis n, g (x i) (x j) := by
    have h := flip_sum i (fun x => g (x i) (x j))
    simpa only [hi, hij'] using h
  have h2 : ∑ x : Basis n, g (x i) (!(x j)) = ∑ x : Basis n, g (x i) (x j) := by
    have h := flip_sum j (fun x => g (x i) (x j))
    simpa only [hj, hji'] using h
  have h3 : ∑ x : Basis n, g (!(x i)) (!(x j)) = ∑ x : Basis n, g (x i) (x j) := by
    have h := flip_sum i (fun x => g (x i) (!(x j)))
    simp only [hi, hij'] at h
    rw [h, h2]
  have h4 : ∑ x : Basis n, (g (x i) (x j) + g (!(x i)) (x j) + g (x i) (!(x j)) +
      g (!(x i)) (!(x j))) =
      ∑ _x : Basis n, (g false false + g false true + g true false + g true true) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    cases x i <;> cases x j <;> simp only [Bool.not_true, Bool.not_false] <;> ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2, h3,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h4
  have h5 : (∑ x : Basis n, g (x i) (x j)) + (∑ x : Basis n, g (x i) (x j)) +
      (∑ x : Basis n, g (x i) (x j)) + (∑ x : Basis n, g (x i) (x j)) =
      cardC n * (g false false + g false true + g true false + g true true) := h4
  have hc := cardC_ne_zero n
  unfold E
  field_simp
  linear_combination h5

/-! ### One- and two-qubit algebra -/

lemma star_ofReal' (r : ℝ) : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r

def perp (f : Bool → ℂ) : Bool → ℂ := fun b => if b then star (f false) else -star (f true)

lemma perp_true (f : Bool → ℂ) : perp f true = star (f false) := by simp [perp]

lemma perp_false (f : Bool → ℂ) : perp f false = -star (f true) := by simp [perp]

def L2 (f g : Bool → ℂ) (a : Label) : ℂ :=
  ∑ p : Bool, star (f p) * localAmplitude a p * g (localFlip a p)

lemma L2_zero (f g : Bool → ℂ) :
    L2 f g 0 = star (f true) * g true + star (f false) * g false := by
  simp only [L2, Fintype.sum_bool, localAmplitude_identity, localFlip_identity, mul_one]

lemma L2_one (f g : Bool → ℂ) :
    L2 f g 1 = star (f true) * g false + star (f false) * g true := by
  simp only [L2, Fintype.sum_bool, localAmplitude_one, localFlip_one, mul_one,
    Bool.not_true, Bool.not_false]

lemma L2_two (f g : Bool → ℂ) :
    L2 f g 2 = star (f true) * Complex.I * g false +
      star (f false) * (-Complex.I) * g true := by
  simp only [L2, Fintype.sum_bool, localAmplitude_two, localFlip_two,
    Bool.not_true, Bool.not_false, ↓reduceIte, Bool.false_eq_true]

lemma L2_three (f g : Bool → ℂ) :
    L2 f g 3 = star (f true) * (-1) * g true + star (f false) * 1 * g false := by
  simp only [L2, Fintype.sum_bool, localAmplitude_three, localFlip_three,
    ↓reduceIte, Bool.false_eq_true]

lemma L2_perp_right_zero (f : Bool → ℂ) : L2 f (perp f) 0 = 0 := by
  rw [L2_zero]
  simp only [perp_true, perp_false]
  ring

lemma L2_perp_left_zero (f : Bool → ℂ) : L2 (perp f) f 0 = 0 := by
  rw [L2_zero]
  simp only [perp_true, perp_false, star_neg, star_star]
  ring

lemma L2_perp_perp_zero (f : Bool → ℂ) : L2 (perp f) (perp f) 0 = L2 f f 0 := by
  rw [L2_zero, L2_zero]
  simp only [perp_true, perp_false, star_neg, star_star]
  ring

lemma L2_perp_perp (f : Bool → ℂ) (a : Label) (ha : a = 1 ∨ a = 2 ∨ a = 3) :
    L2 (perp f) (perp f) a = -L2 f f a := by
  rcases ha with rfl | rfl | rfl
  · rw [L2_one, L2_one]
    simp only [perp_true, perp_false, star_neg, star_star]
    ring
  · rw [L2_two, L2_two]
    simp only [perp_true, perp_false, star_neg, star_star]
    ring
  · rw [L2_three, L2_three]
    simp only [perp_true, perp_false, star_neg, star_star]
    ring

def Phi (c1 c2 : ℂ) (f1 g1 f2 g2 : Bool → ℂ) (p q : Bool) : ℂ :=
  c1 * (f1 p * g1 q) + c2 * (f2 p * g2 q)

lemma Phi_expand (c1 c2 : ℂ) (f1 g1 f2 g2 : Bool → ℂ) (a a' : Label) :
    ∑ p : Bool, ∑ q : Bool, star (Phi c1 c2 f1 g1 f2 g2 p q) *
        (localAmplitude a p * localAmplitude a' q) *
        Phi c1 c2 f1 g1 f2 g2 (localFlip a p) (localFlip a' q) =
      star c1 * c1 * (L2 f1 f1 a * L2 g1 g1 a') +
      star c1 * c2 * (L2 f1 f2 a * L2 g1 g2 a') +
      star c2 * c1 * (L2 f2 f1 a * L2 g2 g1 a') +
      star c2 * c2 * (L2 f2 f2 a * L2 g2 g2 a') := by
  simp only [Phi, L2, Fintype.sum_bool, star_add, star_mul']
  ring

lemma bloch_delta (f g : Bool → ℂ) :
    2 * (star (f false * g true - f true * g false) *
        (f false * g true - f true * g false)) =
      L2 f f 0 * L2 g g 0 - L2 f f 1 * L2 g g 1 - L2 f f 2 * L2 g g 2 -
        L2 f f 3 * L2 g g 3 := by
  rw [L2_zero, L2_zero, L2_one, L2_one, L2_two, L2_two, L2_three, L2_three]
  simp only [star_sub, star_mul']
  linear_combination ((star (f true) * f false - star (f false) * f true) *
    (star (g true) * g false - star (g false) * g true)) * Complex.I_mul_I

def uPh (δ : ℂ) : ℂ := if δ = 0 then 1 else δ / star δ

lemma uPh_norm (δ : ℂ) : star (uPh δ) * uPh δ = 1 := by
  unfold uPh
  by_cases h : δ = 0
  · simp [h]
  · have h' : star δ ≠ 0 := star_ne_zero.mpr h
    rw [if_neg h, star_div₀, star_star]
    field_simp

lemma uPh_mul (δ : ℂ) : uPh δ * star δ = δ := by
  unfold uPh
  by_cases h : δ = 0
  · simp [h]
  · have h' : star δ ≠ 0 := star_ne_zero.mpr h
    rw [if_neg h]
    field_simp

def edgeFun (c1 c2 : ℂ) (f g : Bool → ℂ) (p q : Bool) : ℂ :=
  Phi c1 c2 f g (perp f) (perp g) p q

lemma edge_norm (c1 c2 : ℂ) (f g : Bool → ℂ)
    (hc : star c1 * c1 + star c2 * c2 = 1) (hf : L2 f f 0 = 1) (hg : L2 g g 0 = 1) :
    ∑ p : Bool, ∑ q : Bool, star (edgeFun c1 c2 f g p q) * edgeFun c1 c2 f g p q = 1 := by
  have h := Phi_expand c1 c2 f g (perp f) (perp g) 0 0
  rw [L2_perp_right_zero f, L2_perp_right_zero g, L2_perp_left_zero f, L2_perp_left_zero g,
    L2_perp_perp_zero f, L2_perp_perp_zero g, hf, hg] at h
  simp only [localAmplitude_identity, localFlip_identity] at h
  simp only [edgeFun, Fintype.sum_bool] at h ⊢
  linear_combination h + hc

lemma edge_marg1 (c1 c2 : ℂ) (f g : Bool → ℂ) (hg : L2 g g 0 = 1)
    (a : Label) (ha : a = 1 ∨ a = 2 ∨ a = 3) :
    ∑ p : Bool, ∑ q : Bool, star (edgeFun c1 c2 f g p q) *
        (localAmplitude a p * edgeFun c1 c2 f g (localFlip a p) q) =
      (star c1 * c1 - star c2 * c2) * L2 f f a := by
  have h := Phi_expand c1 c2 f g (perp f) (perp g) a 0
  rw [L2_perp_right_zero g, L2_perp_left_zero g, L2_perp_perp_zero g, hg,
    L2_perp_perp f a ha] at h
  simp only [localAmplitude_identity, localFlip_identity] at h
  simp only [edgeFun, Fintype.sum_bool] at h ⊢
  linear_combination h

lemma edge_marg2 (c1 c2 : ℂ) (f g : Bool → ℂ) (hf : L2 f f 0 = 1)
    (a : Label) (ha : a = 1 ∨ a = 2 ∨ a = 3) :
    ∑ p : Bool, ∑ q : Bool, star (edgeFun c1 c2 f g p q) *
        (localAmplitude a q * edgeFun c1 c2 f g p (localFlip a q)) =
      (star c1 * c1 - star c2 * c2) * L2 g g a := by
  have h := Phi_expand c1 c2 f g (perp f) (perp g) 0 a
  rw [L2_perp_right_zero f, L2_perp_left_zero f, L2_perp_perp_zero f, hf,
    L2_perp_perp g a ha] at h
  simp only [localAmplitude_identity, localFlip_identity] at h
  simp only [edgeFun, Fintype.sum_bool] at h ⊢
  linear_combination h

lemma swap_generic (Φ : Bool → Bool → ℂ) :
    (∑ p : Bool, ∑ q : Bool, star (Φ p q) * Φ p q) -
        ∑ p : Bool, ∑ q : Bool, star (Φ p q) * Φ q p =
      star (Φ false true - Φ true false) * (Φ false true - Φ true false) := by
  simp only [Fintype.sum_bool, star_sub]
  ring

lemma edge_singlet (c1 c2 : ℂ) (f g : Bool → ℂ) :
    edgeFun c1 c2 f g false true - edgeFun c1 c2 f g true false =
      c1 * (f false * g true - f true * g false) +
        c2 * star (f false * g true - f true * g false) := by
  simp only [edgeFun, Phi, perp_true, perp_false, star_sub, star_mul']
  ring

lemma coef_norm (c s : ℝ) (u : ℂ) (hcs : c ^ 2 + s ^ 2 = 1) (hu : star u * u = 1) :
    star (c : ℂ) * (c : ℂ) + star ((s : ℂ) * u) * ((s : ℂ) * u) = 1 := by
  have hcs' : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  rw [star_mul', star_ofReal', star_ofReal']
  linear_combination hcs' + (s : ℂ) ^ 2 * hu

lemma coef_kappa (c s : ℝ) (u : ℂ) (hu : star u * u = 1) :
    star (c : ℂ) * (c : ℂ) - star ((s : ℂ) * u) * ((s : ℂ) * u) =
      ((c ^ 2 - s ^ 2 : ℝ) : ℂ) := by
  rw [star_mul', star_ofReal', star_ofReal']
  push_cast
  linear_combination -(s : ℂ) ^ 2 * hu

lemma edge_swap (c s : ℝ) (u : ℂ) (f g : Bool → ℂ) (hcs : c ^ 2 + s ^ 2 = 1)
    (hu : star u * u = 1)
    (huδ : u * star (f false * g true - f true * g false) =
      f false * g true - f true * g false)
    (hf : L2 f f 0 = 1) (hg : L2 g g 0 = 1) :
    ∑ p : Bool, ∑ q : Bool, star (edgeFun (c : ℂ) ((s : ℂ) * u) f g p q) *
        edgeFun (c : ℂ) ((s : ℂ) * u) f g q p =
      ((1 - (c + s) ^ 2 * Complex.normSq (f false * g true - f true * g false) : ℝ) : ℂ) := by
  have hn := edge_norm (c : ℂ) ((s : ℂ) * u) f g (coef_norm c s u hcs hu) hf hg
  have hgen := swap_generic (edgeFun (c : ℂ) ((s : ℂ) * u) f g)
  have h1 : (c : ℂ) * (f false * g true - f true * g false) +
      (s : ℂ) * u * star (f false * g true - f true * g false) =
      ((c : ℂ) + (s : ℂ)) * (f false * g true - f true * g false) := by
    rw [mul_assoc, huδ]
    ring
  have hst : star ((c : ℂ) + (s : ℂ)) = (c : ℂ) + (s : ℂ) := by
    rw [star_add, star_ofReal', star_ofReal']
  rw [hn, edge_singlet, h1, star_mul', hst] at hgen
  have hd : star (f false * g true - f true * g false) *
      (f false * g true - f true * g false) =
      (Complex.normSq (f false * g true - f true * g false) : ℂ) := by
    simpa only [Complex.star_def] using
      (Complex.normSq_eq_conj_mul_self (z := f false * g true - f true * g false)).symm
  push_cast
  linear_combination -hgen - ((c : ℂ) + (s : ℂ)) ^ 2 * hd

lemma normSq_delta (f g : Bool → ℂ) (rf rg : Fin 3 → ℝ)
    (hf0 : L2 f f 0 = 1) (hf1 : L2 f f 1 = (rf 0 : ℂ)) (hf2 : L2 f f 2 = (rf 1 : ℂ))
    (hf3 : L2 f f 3 = (rf 2 : ℂ))
    (hg0 : L2 g g 0 = 1) (hg1 : L2 g g 1 = (rg 0 : ℂ)) (hg2 : L2 g g 2 = (rg 1 : ℂ))
    (hg3 : L2 g g 3 = (rg 2 : ℂ)) :
    Complex.normSq (f false * g true - f true * g false) =
      (1 - ∑ a : Fin 3, rf a * rg a) / 2 := by
  have h := bloch_delta f g
  have hd : star (f false * g true - f true * g false) *
      (f false * g true - f true * g false) =
      (Complex.normSq (f false * g true - f true * g false) : ℂ) := by
    simpa only [Complex.star_def] using
      (Complex.normSq_eq_conj_mul_self (z := f false * g true - f true * g false)).symm
  rw [hf0, hg0, hf1, hg1, hf2, hg2, hf3, hg3, hd] at h
  have h' : 2 * Complex.normSq (f false * g true - f true * g false) =
      1 * 1 - rf 0 * rg 0 - rf 1 * rg 1 - rf 2 * rg 2 := by exact_mod_cast h
  rw [Fin.sum_univ_three]
  linarith

/-! ### The concrete block system -/

def rt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)

lemma rt2_star : star rt2 = rt2 := star_ofReal' _

lemma rt2_mul : rt2 * rt2 = 2 := by
  unfold rt2
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

def sel (b : Bool) (f : Bool → ℂ) : Bool → ℂ := if b then f else perp f

def Uset {n : ℕ} (M : Finset (Edge n)) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ∀ e ∈ M, v ≠ e.val.1 ∧ v ≠ e.val.2)

def blocks {n : ℕ} (M : Finset (Edge n)) : Finset (Edge n ⊕ Fin n) :=
  M.disjSum (Uset M)

lemma mem_blocks_inl {n : ℕ} {M : Finset (Edge n)} {e : Edge n} :
    Sum.inl e ∈ blocks M ↔ e ∈ M := Finset.inl_mem_disjSum

lemma mem_blocks_inr {n : ℕ} {M : Finset (Edge n)} {v : Fin n} :
    Sum.inr v ∈ blocks M ↔ v ∈ Uset M := Finset.inr_mem_disjSum

def supp {n : ℕ} : Edge n ⊕ Fin n → Finset (Fin n)
  | Sum.inl e => {e.val.1, e.val.2}
  | Sum.inr v => {v}

def fam {n : ℕ} (χ : Fin n → Bool → ℂ) (c1 : ℂ) (c2 : Edge n → ℂ) (ε : Fin n → Bool) :
    Edge n ⊕ Fin n → Basis n → ℂ
  | Sum.inl e => fun x =>
      2 * edgeFun c1 (c2 e) (χ e.val.1) (χ e.val.2) (x e.val.1) (x e.val.2)
  | Sum.inr v => fun x => rt2 * sel (ε v) (χ v) (x v)

lemma sel_L2_zero (b : Bool) (f : Bool → ℂ) (hf : L2 f f 0 = 1) :
    L2 (sel b f) (sel b f) 0 = 1 := by
  cases b
  · simp only [sel, ↓reduceIte, Bool.false_eq_true, L2_perp_perp_zero, hf]
  · simp only [sel, ↓reduceIte, hf]

lemma sel_L2 (b : Bool) (f : Bool → ℂ) (a : Label) (ha : a = 1 ∨ a = 2 ∨ a = 3) :
    L2 (sel b f) (sel b f) a = (if b then 1 else -1) * L2 f f a := by
  cases b
  · simp only [sel, ↓reduceIte, Bool.false_eq_true, L2_perp_perp f a ha]
    ring
  · simp only [sel, ↓reduceIte]
    ring

lemma fam_sys {n : ℕ} (χ : Fin n → Bool → ℂ) (c1 : ℂ) (c2 : Edge n → ℂ)
    (ε : Fin n → Bool) (M : Finset (Edge n))
    (hχ : ∀ v, L2 (χ v) (χ v) 0 = 1)
    (hM : ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
      e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2)
    (hc : ∀ e, star c1 * c1 + star (c2 e) * c2 e = 1) :
    Sys (blocks M) supp (fam χ c1 c2 ε) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (e | v) _ x y h
    · show 2 * edgeFun c1 (c2 e) (χ e.val.1) (χ e.val.2) (x e.val.1) (x e.val.2) =
        2 * edgeFun c1 (c2 e) (χ e.val.1) (χ e.val.2) (y e.val.1) (y e.val.2)
      rw [h e.val.1 (by simp [supp]), h e.val.2 (by simp [supp])]
    · show rt2 * sel (ε v) (χ v) (x v) = rt2 * sel (ε v) (χ v) (y v)
      rw [h v (by simp [supp])]
  · rintro (e | v) hc1 (e' | v') hc2 hne
    · have he := mem_blocks_inl.mp hc1
      have he' := mem_blocks_inl.mp hc2
      have hee : e ≠ e' := fun h => hne (by rw [h])
      obtain ⟨h1, h2, h3, h4⟩ := hM e he e' he' hee
      rw [Finset.disjoint_left]
      intro k hk hk'
      simp only [supp, Finset.mem_insert, Finset.mem_singleton] at hk hk'
      rcases hk with rfl | rfl <;> rcases hk' with h | h
      exacts [h1 h, h2 h, h3 h, h4 h]
    · have hv := (Finset.mem_filter.mp (mem_blocks_inr.mp hc2)).2 e (mem_blocks_inl.mp hc1)
      rw [Finset.disjoint_left]
      intro k hk hk'
      simp only [supp, Finset.mem_insert, Finset.mem_singleton] at hk hk'
      subst hk'
      rcases hk with h | h
      exacts [hv.1 h, hv.2 h]
    · have hv := (Finset.mem_filter.mp (mem_blocks_inr.mp hc1)).2 e' (mem_blocks_inl.mp hc2)
      rw [Finset.disjoint_left]
      intro k hk hk'
      simp only [supp, Finset.mem_insert, Finset.mem_singleton] at hk hk'
      subst hk
      rcases hk' with h | h
      exacts [hv.1 h, hv.2 h]
    · have hvv : v ≠ v' := fun h => hne (by rw [h])
      rw [Finset.disjoint_left]
      intro k hk hk'
      simp only [supp, Finset.mem_singleton] at hk hk'
      exact hvv (hk.symm.trans hk')
  · rintro (e | v) _
    · have hne : e.val.1 ≠ e.val.2 := ne_of_lt e.property
      have hn := edge_norm c1 (c2 e) (χ e.val.1) (χ e.val.2) (hc e) (hχ _) (hχ _)
      have hE := E_coord2 (n := n) e.val.1 e.val.2 hne
        (fun p q => star (2 * edgeFun c1 (c2 e) (χ e.val.1) (χ e.val.2) p q) *
          (2 * edgeFun c1 (c2 e) (χ e.val.1) (χ e.val.2) p q))
      refine hE.trans ?_
      simp only [star_mul', star_ofNat]
      simp only [Fintype.sum_bool] at hn
      linear_combination hn
    · have hs := sel_L2_zero (ε v) (χ v) (hχ v)
      rw [L2_zero] at hs
      have hE := E_coord (n := n) v
        (fun b => star (rt2 * sel (ε v) (χ v) b) * (rt2 * sel (ε v) (χ v) b))
      refine hE.trans ?_
      simp only [star_mul', rt2_star]
      linear_combination ((star (sel (ε v) (χ v) true) * sel (ε v) (χ v) true +
        star (sel (ε v) (χ v) false) * sel (ε v) (χ v) false) / 2) * rt2_mul + hs

lemma marg_edge1 {n : ℕ} (χ : Fin n → Bool → ℂ) (c1 : ℂ) (c2 : Edge n → ℂ)
    (ε : Fin n → Bool) (hχ : ∀ v, L2 (χ v) (χ v) 0 = 1) (e : Edge n)
    (a : Label) (ha : a = 1 ∨ a = 2 ∨ a = 3) :
    E (fun x => star (fam χ c1 c2 ε (Sum.inl e) x) *
        sOp a e.val.1 (fam χ c1 c2 ε (Sum.inl e)) x) =
      (star c1 * c1 - star (c2 e) * c2 e) * L2 (χ e.val.1) (χ e.val.1) a := by
  have hne : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  have hm := edge_marg1 c1 (c2 e) (χ e.val.1) (χ e.val.2) (hχ _) a ha
  have hE := E_coord2 (n := n) e.val.1 e.val.2 hne
    (fun p q => star (2 * edgeFun c1 (c2 e) (χ e.val.1) (χ e.val.2) p q) *
      (localAmplitude a p *
        (2 * edgeFun c1 (c2 e) (χ e.val.1) (χ e.val.2) (localFlip a p) q)))
  have hfun : (fun x : Basis n => star (fam χ c1 c2 ε (Sum.inl e) x) *
      sOp a e.val.1 (fam χ c1 c2 ε (Sum.inl e)) x) =
      fun x => star (2 * edgeFun c1 (c2 e) (χ e.val.1) (χ e.val.2) (x e.val.1) (x e.val.2)) *
        (localAmplitude a (x e.val.1) * (2 * edgeFun c1 (c2 e) (χ e.val.1) (χ e.val.2)
          (localFlip a (x e.val.1)) (x e.val.2))) := by
    funext x
    simp only [fam, sOp, Function.update_self, Function.update_of_ne hne.symm]
  rw [hfun, hE]
  simp only [star_mul', star_ofNat]
  simp only [Fintype.sum_bool] at hm
  linear_combination hm

lemma marg_edge2 {n : ℕ} (χ : Fin n → Bool → ℂ) (c1 : ℂ) (c2 : Edge n → ℂ)
    (ε : Fin n → Bool) (hχ : ∀ v, L2 (χ v) (χ v) 0 = 1) (e : Edge n)
    (a : Label) (ha : a = 1 ∨ a = 2 ∨ a = 3) :
    E (fun x => star (fam χ c1 c2 ε (Sum.inl e) x) *
        sOp a e.val.2 (fam χ c1 c2 ε (Sum.inl e)) x) =
      (star c1 * c1 - star (c2 e) * c2 e) * L2 (χ e.val.2) (χ e.val.2) a := by
  have hne : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  have hm := edge_marg2 c1 (c2 e) (χ e.val.1) (χ e.val.2) (hχ _) a ha
  have hE := E_coord2 (n := n) e.val.1 e.val.2 hne
    (fun p q => star (2 * edgeFun c1 (c2 e) (χ e.val.1) (χ e.val.2) p q) *
      (localAmplitude a q *
        (2 * edgeFun c1 (c2 e) (χ e.val.1) (χ e.val.2) p (localFlip a q))))
  have hfun : (fun x : Basis n => star (fam χ c1 c2 ε (Sum.inl e) x) *
      sOp a e.val.2 (fam χ c1 c2 ε (Sum.inl e)) x) =
      fun x => star (2 * edgeFun c1 (c2 e) (χ e.val.1) (χ e.val.2) (x e.val.1) (x e.val.2)) *
        (localAmplitude a (x e.val.2) * (2 * edgeFun c1 (c2 e) (χ e.val.1) (χ e.val.2)
          (x e.val.1) (localFlip a (x e.val.2)))) := by
    funext x
    simp only [fam, sOp, Function.update_self, Function.update_of_ne hne]
  rw [hfun, hE]
  simp only [star_mul', star_ofNat]
  simp only [Fintype.sum_bool] at hm
  linear_combination hm

lemma marg_vertex {n : ℕ} (χ : Fin n → Bool → ℂ) (c1 : ℂ) (c2 : Edge n → ℂ)
    (ε : Fin n → Bool) (v : Fin n) (a : Label) (ha : a = 1 ∨ a = 2 ∨ a = 3) :
    E (fun x => star (fam χ c1 c2 ε (Sum.inr v) x) *
        sOp a v (fam χ c1 c2 ε (Sum.inr v)) x) =
      (if ε v then 1 else -1) * L2 (χ v) (χ v) a := by
  have hs := sel_L2 (ε v) (χ v) a ha
  have hE := E_coord (n := n) v
    (fun b => star (rt2 * sel (ε v) (χ v) b) *
      (localAmplitude a b * (rt2 * sel (ε v) (χ v) (localFlip a b))))
  have hfun : (fun x : Basis n => star (fam χ c1 c2 ε (Sum.inr v) x) *
      sOp a v (fam χ c1 c2 ε (Sum.inr v)) x) =
      fun x => star (rt2 * sel (ε v) (χ v) (x v)) *
        (localAmplitude a (x v) * (rt2 * sel (ε v) (χ v) (localFlip a (x v)))) := by
    funext x
    simp only [fam, sOp, Function.update_self]
  rw [hfun, hE, ← hs]
  simp only [L2, Fintype.sum_bool, star_mul', rt2_star]
  linear_combination ((star (sel (ε v) (χ v) true) * localAmplitude a true *
      sel (ε v) (χ v) (localFlip a true) +
    star (sel (ε v) (χ v) false) * localAmplitude a false *
      sel (ε v) (χ v) (localFlip a false)) / 2) * rt2_mul

def gR {n : ℕ} (M : Finset (Edge n)) (κ : ℝ) (v : Fin n) (b : Bool) : ℝ :=
  if v ∈ Uset M then (if b then 1 else -1) else κ

lemma marg {n : ℕ} (χ : Fin n → Bool → ℂ) (c1 : ℂ) (c2 : Edge n → ℂ)
    (ε : Fin n → Bool) (M : Finset (Edge n)) (κ : ℝ)
    (hχ : ∀ v, L2 (χ v) (χ v) 0 = 1)
    (hκ : ∀ e, star c1 * c1 - star (c2 e) * c2 e = (κ : ℂ)) (v : Fin n) :
    ∃ b ∈ blocks M, v ∈ supp b ∧ ∀ a : Label, (a = 1 ∨ a = 2 ∨ a = 3) →
      E (fun x => star (fam χ c1 c2 ε b x) * sOp a v (fam χ c1 c2 ε b) x) =
        ((gR M κ v (ε v) : ℝ) : ℂ) * L2 (χ v) (χ v) a := by
  by_cases hv : v ∈ Uset M
  · refine ⟨Sum.inr v, mem_blocks_inr.mpr hv, by simp [supp], fun a ha => ?_⟩
    rw [marg_vertex χ c1 c2 ε v a ha]
    simp only [gR, if_pos hv]
    cases ε v <;> simp
  · have hex : ∃ e ∈ M, v = e.val.1 ∨ v = e.val.2 := by
      by_contra hcon
      apply hv
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and]
      intro e he
      exact ⟨fun h => hcon ⟨e, he, Or.inl h⟩, fun h => hcon ⟨e, he, Or.inr h⟩⟩
    obtain ⟨e, he, h | h⟩ := hex
    · refine ⟨Sum.inl e, mem_blocks_inl.mpr he, by simp [supp, h], fun a ha => ?_⟩
      subst h
      rw [marg_edge1 χ c1 c2 ε hχ e a ha, hκ e]
      simp only [gR, if_neg hv]
    · refine ⟨Sum.inl e, mem_blocks_inl.mpr he, by simp [supp, h], fun a ha => ?_⟩
      subst h
      rw [marg_edge2 χ c1 c2 ε hχ e a ha, hκ e]
      simp only [gR, if_neg hv]

lemma same_block_edge {n : ℕ} (M : Finset (Edge n)) (e : Edge n) (b : Edge n ⊕ Fin n)
    (hb : b ∈ blocks M) (h1 : e.val.1 ∈ supp b) (h2 : e.val.2 ∈ supp b) : e ∈ M := by
  have he := e.property
  rcases b with f | v
  · have hf := mem_blocks_inl.mp hb
    have hf' := f.property
    simp only [supp, Finset.mem_insert, Finset.mem_singleton] at h1 h2
    have hef : e.val.1 = f.val.1 ∧ e.val.2 = f.val.2 := by
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (h1.trans h2.symm) (ne_of_lt he)
      · exact ⟨h1, h2⟩
      · rw [h1, h2] at he
        exact absurd he (lt_asymm hf')
      · exact absurd (h1.trans h2.symm) (ne_of_lt he)
    have : e = f := Subtype.ext (Prod.ext hef.1 hef.2)
    rw [this]
    exact hf
  · simp only [supp, Finset.mem_singleton] at h1 h2
    exact absurd (h1.trans h2.symm) (ne_of_lt he)

/-! ### The witness wave and its pair energies -/

def delta {n : ℕ} (χ : Fin n → Bool → ℂ) (e : Edge n) : ℂ :=
  χ e.val.1 false * χ e.val.2 true - χ e.val.1 true * χ e.val.2 false

def psi {n : ℕ} (χ : Fin n → Bool → ℂ) (M : Finset (Edge n)) (c s : ℝ)
    (ε : Fin n → Bool) : Wave n :=
  blockWave (blocks M) (fam χ (c : ℂ) (fun e => (s : ℂ) * uPh (delta χ e)) ε)

lemma psi_sys {n : ℕ} (χ : Fin n → Bool → ℂ) (M : Finset (Edge n)) (c s : ℝ)
    (ε : Fin n → Bool) (hχ : ∀ v, L2 (χ v) (χ v) 0 = 1)
    (hM : ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
      e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    Sys (blocks M) supp (fam χ (c : ℂ) (fun e => (s : ℂ) * uPh (delta χ e)) ε) :=
  fam_sys χ (c : ℂ) (fun e => (s : ℂ) * uPh (delta χ e)) ε M hχ hM
    (fun e => coef_norm c s _ hcs (uPh_norm _))

lemma psi_matched {n : ℕ} (χ : Fin n → Bool → ℂ) (r : Fin n → Fin 3 → ℝ)
    (M : Finset (Edge n)) (c s : ℝ) (ε : Fin n → Bool)
    (hχ0 : ∀ v, L2 (χ v) (χ v) 0 = 1) (hχ1 : ∀ v, L2 (χ v) (χ v) 1 = (r v 0 : ℂ))
    (hχ2 : ∀ v, L2 (χ v) (χ v) 2 = (r v 1 : ℂ)) (hχ3 : ∀ v, L2 (χ v) (χ v) 3 = (r v 2 : ℂ))
    (hM : ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
      e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2)
    (hcs : c ^ 2 + s ^ 2 = 1) (e : Edge n) (he : e ∈ M) :
    pairEnergy e.val.1 e.val.2 (psi χ M c s ε) =
      Nr n * ((1 + 2 * c * s) * (1 - ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2) := by
  have hsys := psi_sys χ M c s ε hχ0 hM hcs
  have hne : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  have hsw := edge_swap c s (uPh (delta χ e)) (χ e.val.1) (χ e.val.2) hcs (uPh_norm _)
    (uPh_mul (delta χ e)) (hχ0 _) (hχ0 _)
  have hE := E_coord2 (n := n) e.val.1 e.val.2 hne
    (fun p q => star (2 * edgeFun (c : ℂ) ((s : ℂ) * uPh (delta χ e))
        (χ e.val.1) (χ e.val.2) p q) *
      (2 * edgeFun (c : ℂ) ((s : ℂ) * uPh (delta χ e)) (χ e.val.1) (χ e.val.2) q p))
  have hfun : (fun x : Basis n =>
      star (fam χ (c : ℂ) (fun e => (s : ℂ) * uPh (delta χ e)) ε (Sum.inl e) x) *
        (1 * fam χ (c : ℂ) (fun e => (s : ℂ) * uPh (delta χ e)) ε (Sum.inl e)
          (x ∘ Equiv.swap e.val.1 e.val.2))) =
      fun x => star (2 * edgeFun (c : ℂ) ((s : ℂ) * uPh (delta χ e))
          (χ e.val.1) (χ e.val.2) (x e.val.1) (x e.val.2)) *
        (2 * edgeFun (c : ℂ) ((s : ℂ) * uPh (delta χ e)) (χ e.val.1) (χ e.val.2)
          (x e.val.2) (x e.val.1)) := by
    funext x
    simp only [fam, Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      one_mul]
  have hv : E (fun x : Basis n =>
      star (fam χ (c : ℂ) (fun e => (s : ℂ) * uPh (delta χ e)) ε (Sum.inl e) x) *
        (1 * fam χ (c : ℂ) (fun e => (s : ℂ) * uPh (delta χ e)) ε (Sum.inl e)
          (x ∘ Equiv.swap e.val.1 e.val.2))) =
      ((1 - (c + s) ^ 2 * Complex.normSq (χ e.val.1 false * χ e.val.2 true -
        χ e.val.1 true * χ e.val.2 false) : ℝ) : ℂ) := by
    rw [hfun, hE, ← hsw]
    simp only [star_mul', star_ofNat, Fintype.sum_bool]
    ring
  have hmain := hsys.pairEnergy_same (mem_blocks_inl.mpr he)
    (i := e.val.1) (j := e.val.2) (by simp [supp]) (by simp [supp]) _ hv
  have hδ := normSq_delta (χ e.val.1) (χ e.val.2) (r e.val.1) (r e.val.2)
    (hχ0 _) (hχ1 _) (hχ2 _) (hχ3 _) (hχ0 _) (hχ1 _) (hχ2 _) (hχ3 _)
  rw [hδ] at hmain
  unfold psi
  rw [hmain]
  linear_combination (Nr n * (1 - ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2) * hcs

lemma psi_cross {n : ℕ} (χ : Fin n → Bool → ℂ) (r : Fin n → Fin 3 → ℝ)
    (M : Finset (Edge n)) (c s : ℝ) (ε : Fin n → Bool)
    (hχ0 : ∀ v, L2 (χ v) (χ v) 0 = 1) (hχ1 : ∀ v, L2 (χ v) (χ v) 1 = (r v 0 : ℂ))
    (hχ2 : ∀ v, L2 (χ v) (χ v) 2 = (r v 1 : ℂ)) (hχ3 : ∀ v, L2 (χ v) (χ v) 3 = (r v 2 : ℂ))
    (hM : ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
      e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2)
    (hcs : c ^ 2 + s ^ 2 = 1) (e : Edge n) (he : e ∉ M) :
    pairEnergy e.val.1 e.val.2 (psi χ M c s ε) =
      Nr n * ((1 - gR M (c ^ 2 - s ^ 2) e.val.1 (ε e.val.1) *
        gR M (c ^ 2 - s ^ 2) e.val.2 (ε e.val.2) *
        ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2) := by
  have hsys := psi_sys χ M c s ε hχ0 hM hcs
  have hκ : ∀ e : Edge n, star (c : ℂ) * (c : ℂ) -
      star ((fun e => (s : ℂ) * uPh (delta χ e)) e) *
        (fun e => (s : ℂ) * uPh (delta χ e)) e = ((c ^ 2 - s ^ 2 : ℝ) : ℂ) :=
    fun e => coef_kappa c s _ (uPh_norm _)
  obtain ⟨b, hb, hib, hmb⟩ := marg χ (c : ℂ) (fun e => (s : ℂ) * uPh (delta χ e)) ε M
    (c ^ 2 - s ^ 2) hχ0 hκ e.val.1
  obtain ⟨b', hb', hjb', hmb'⟩ := marg χ (c : ℂ) (fun e => (s : ℂ) * uPh (delta χ e)) ε M
    (c ^ 2 - s ^ 2) hχ0 hκ e.val.2
  have hbb : b ≠ b' := by
    intro h
    subst h
    exact he (same_block_edge M e b hb hib hjb')
  have hmain := hsys.pairEnergy_cross hb hb' hbb hib hjb' (ne_of_lt e.property)
    (gR M (c ^ 2 - s ^ 2) e.val.1 (ε e.val.1) * r e.val.1 0)
    (gR M (c ^ 2 - s ^ 2) e.val.1 (ε e.val.1) * r e.val.1 1)
    (gR M (c ^ 2 - s ^ 2) e.val.1 (ε e.val.1) * r e.val.1 2)
    (gR M (c ^ 2 - s ^ 2) e.val.2 (ε e.val.2) * r e.val.2 0)
    (gR M (c ^ 2 - s ^ 2) e.val.2 (ε e.val.2) * r e.val.2 1)
    (gR M (c ^ 2 - s ^ 2) e.val.2 (ε e.val.2) * r e.val.2 2)
    (by rw [hmb 1 (Or.inl rfl), hχ1, Complex.ofReal_mul])
    (by rw [hmb 2 (Or.inr (Or.inl rfl)), hχ2, Complex.ofReal_mul])
    (by rw [hmb 3 (Or.inr (Or.inr rfl)), hχ3, Complex.ofReal_mul])
    (by rw [hmb' 1 (Or.inl rfl), hχ1, Complex.ofReal_mul])
    (by rw [hmb' 2 (Or.inr (Or.inl rfl)), hχ2, Complex.ofReal_mul])
    (by rw [hmb' 3 (Or.inr (Or.inr rfl)), hχ3, Complex.ofReal_mul])
  unfold psi
  rw [hmain, Fin.sum_univ_three]
  ring

/-! ### Scaling and the optimum -/

lemma squaredNorm_realScale {n : ℕ} (a : ℝ) (ψ : Wave n) :
    squaredNorm (realScale a ψ) = a ^ 2 * squaredNorm ψ := by
  unfold squaredNorm realScale
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  ring

lemma energy_realScale {n : ℕ} (w : Weights n) (a : ℝ) (ψ : Wave n) :
    energy w (realScale a ψ) = a ^ 2 * energy w ψ := by
  unfold energy realScale
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hx : ∀ x : Basis n, Complex.normSq ((a : ℂ) * ψ x -
      (a : ℂ) * ψ (x ∘ Equiv.swap e.val.1 e.val.2)) =
      a ^ 2 * Complex.normSq (ψ x - ψ (x ∘ Equiv.swap e.val.1 e.val.2)) := by
    intro x
    rw [← mul_sub, Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  simp only [hx]
  rw [← Finset.mul_sum]
  ring

lemma energy_le_of_norm {n : ℕ} (w : Weights n) (Ψ : Wave n) (N : ℝ) (hN : 0 < N)
    (h : squaredNorm Ψ = N) : energy w Ψ ≤ N * optimum ⟨n, w⟩ := by
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN.le
  have hinv : ((Real.sqrt N)⁻¹) ^ 2 = N⁻¹ := by rw [inv_pow, hsq]
  have h1 : squaredNorm (realScale (Real.sqrt N)⁻¹ Ψ) = 1 := by
    rw [squaredNorm_realScale, h, hinv]
    exact inv_mul_cancel₀ hN.ne'
  have h2 : energy w (realScale (Real.sqrt N)⁻¹ Ψ) ≤ optimum ⟨n, w⟩ :=
    energy_le_optimum ⟨n, w⟩ _ h1
  rw [energy_realScale, hinv] at h2
  calc energy w Ψ = N * (N⁻¹ * energy w Ψ) := by
        field_simp
    _ ≤ N * optimum ⟨n, w⟩ := mul_le_mul_of_nonneg_left h2 hN.le

/-! ### Averaging over the signs of the unmatched vertices -/

def qW (κ : ℝ) (b : Bool) : ℝ := if b then (1 + κ) / 2 else (1 - κ) / 2

def pW (n : ℕ) (κ : ℝ) (ε : Fin n → Bool) : ℝ := ∏ v, qW κ (ε v)

lemma qW_sum (κ : ℝ) : qW κ true + qW κ false = 1 := by
  simp only [qW, ↓reduceIte, Bool.false_eq_true]
  ring

lemma pW_nonneg (n : ℕ) (κ : ℝ) (h1 : -1 ≤ κ) (h2 : κ ≤ 1) (ε : Fin n → Bool) :
    0 ≤ pW n κ ε := by
  refine Finset.prod_nonneg fun v _ => ?_
  unfold qW
  split_ifs <;> linarith

lemma pW_sum (n : ℕ) (κ : ℝ) : ∑ ε : Fin n → Bool, pW n κ ε = 1 := by
  unfold pW
  rw [← Fintype.prod_sum (fun (_ : Fin n) (b : Bool) => qW κ b)]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [Fintype.sum_bool]
  exact qW_sum κ

lemma pW_avg2 (n : ℕ) (κ : ℝ) {i j : Fin n} (hij : i ≠ j) (g h : Bool → ℝ) :
    ∑ ε : Fin n → Bool, pW n κ ε * (g (ε i) * h (ε j)) =
      (qW κ true * g true + qW κ false * g false) *
        (qW κ true * h true + qW κ false * h false) := by
  classical
  have hterm : ∀ ε : Fin n → Bool, pW n κ ε * (g (ε i) * h (ε j)) =
      ∏ v, (qW κ (ε v) * ((if v = i then g (ε v) else 1) *
        (if v = j then h (ε v) else 1))) := by
    intro ε
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    simp [pW]
  have hfac : ∀ v : Fin n, (∑ b : Bool, qW κ b * ((if v = i then g b else 1) *
      (if v = j then h b else 1))) =
      (if v = i then qW κ true * g true + qW κ false * g false else 1) *
        (if v = j then qW κ true * h true + qW κ false * h false else 1) := by
    intro v
    rw [Fintype.sum_bool]
    by_cases hi : v = i
    · subst hi
      simp [hij]
    · by_cases hj : v = j
      · subst hj
        simp [hi]
      · simp [hi, hj, qW_sum κ]
  calc ∑ ε : Fin n → Bool, pW n κ ε * (g (ε i) * h (ε j))
      = ∑ ε : Fin n → Bool, ∏ v, (qW κ (ε v) * ((if v = i then g (ε v) else 1) *
          (if v = j then h (ε v) else 1))) := Finset.sum_congr rfl fun ε _ => hterm ε
    _ = ∏ v : Fin n, ∑ b : Bool, qW κ b * ((if v = i then g b else 1) *
          (if v = j then h b else 1)) :=
        (Fintype.prod_sum (fun (v : Fin n) (b : Bool) =>
          qW κ b * ((if v = i then g b else 1) * (if v = j then h b else 1)))).symm
    _ = ∏ v : Fin n, ((if v = i then qW κ true * g true + qW κ false * g false else 1) *
          (if v = j then qW κ true * h true + qW κ false * h false else 1)) :=
        Finset.prod_congr rfl fun v _ => hfac v
    _ = _ := by
        rw [Finset.prod_mul_distrib]
        simp

lemma gR_avg {n : ℕ} (M : Finset (Edge n)) (κ : ℝ) (v : Fin n) :
    qW κ true * gR M κ v true + qW κ false * gR M κ v false = κ := by
  unfold gR qW
  by_cases hv : v ∈ Uset M
  · simp only [if_pos hv, ↓reduceIte, Bool.false_eq_true]
    ring
  · simp only [if_neg hv, ↓reduceIte, Bool.false_eq_true]
    ring

lemma avg_total (n : ℕ) (κ N A : ℝ) (D : Finset (Edge n)) (w t : Edge n → ℝ)
    (G : Fin n → Bool → ℝ)
    (hG : ∀ v, qW κ true * G v true + qW κ false * G v false = κ) :
    ∑ ε : Fin n → Bool, pW n κ ε * (N * (A + ∑ e ∈ D, w e *
        ((1 - G e.val.1 (ε e.val.1) * G e.val.2 (ε e.val.2) * t e) / 2))) =
      N * (A + ∑ e ∈ D, w e * ((1 - κ ^ 2 * t e) / 2)) := by
  have hb := pW_sum n κ
  have h1 : ∀ e : Edge n, ∑ ε : Fin n → Bool, pW n κ ε * (w e *
      ((1 - G e.val.1 (ε e.val.1) * G e.val.2 (ε e.val.2) * t e) / 2)) =
      w e * ((1 - κ ^ 2 * t e) / 2) := by
    intro e
    have ha := pW_avg2 n κ (ne_of_lt e.property) (G e.val.1) (G e.val.2)
    rw [hG, hG] at ha
    calc ∑ ε : Fin n → Bool, pW n κ ε * (w e *
          ((1 - G e.val.1 (ε e.val.1) * G e.val.2 (ε e.val.2) * t e) / 2))
        = ∑ ε : Fin n → Bool, (w e / 2 * pW n κ ε - w e * t e / 2 *
            (pW n κ ε * (G e.val.1 (ε e.val.1) * G e.val.2 (ε e.val.2)))) :=
          Finset.sum_congr rfl fun ε _ => by ring
      _ = w e * ((1 - κ ^ 2 * t e) / 2) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ha, hb]
          ring
  have hS : ∑ ε : Fin n → Bool, pW n κ ε * ∑ e ∈ D, w e *
      ((1 - G e.val.1 (ε e.val.1) * G e.val.2 (ε e.val.2) * t e) / 2) =
      ∑ e ∈ D, w e * ((1 - κ ^ 2 * t e) / 2) := by
    calc ∑ ε : Fin n → Bool, pW n κ ε * ∑ e ∈ D, w e *
          ((1 - G e.val.1 (ε e.val.1) * G e.val.2 (ε e.val.2) * t e) / 2)
        = ∑ ε : Fin n → Bool, ∑ e ∈ D, pW n κ ε * (w e *
          ((1 - G e.val.1 (ε e.val.1) * G e.val.2 (ε e.val.2) * t e) / 2)) :=
          Finset.sum_congr rfl fun ε _ => Finset.mul_sum _ _ _
      _ = ∑ e ∈ D, ∑ ε : Fin n → Bool, pW n κ ε * (w e *
          ((1 - G e.val.1 (ε e.val.1) * G e.val.2 (ε e.val.2) * t e) / 2)) :=
          Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun e _ => h1 e
  calc ∑ ε : Fin n → Bool, pW n κ ε * (N * (A + ∑ e ∈ D, w e *
        ((1 - G e.val.1 (ε e.val.1) * G e.val.2 (ε e.val.2) * t e) / 2)))
      = ∑ ε : Fin n → Bool, (N * A * pW n κ ε + N * (pW n κ ε * ∑ e ∈ D, w e *
        ((1 - G e.val.1 (ε e.val.1) * G e.val.2 (ε e.val.2) * t e) / 2))) :=
        Finset.sum_congr rfl fun ε _ => by ring
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hb, hS]
        ring

theorem main_bound {n : ℕ}
    (w : Weights n) (r : Fin n → Fin 3 → ℝ)
    (hr : ∀ i, ∑ a : Fin 3, (r i a) ^ 2 = 1)
    (M : Finset (Edge n))
    (hM : ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
      e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2)
    (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (∑ e ∈ M, (w e : ℝ) * ((1 + 2 * c * s) *
        (1 - ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2)) +
      (∑ e ∈ Finset.univ \ M, (w e : ℝ) *
        ((1 - (c ^ 2 - s ^ 2) ^ 2 * ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2)) ≤
      optimum ⟨n, w⟩ := by
  classical
  have hlocal (i : Fin n) := qubit_of_unit_bloch (r i 0) (r i 1) (r i 2)
    (by simpa only [Fin.sum_univ_three] using hr i)
  choose χ hχn hχ1 hχ2 hχ3 using hlocal
  have hχ0 : ∀ v, L2 (χ v) (χ v) 0 = 1 := fun v => localExpectation_identity (χ v) (hχn v)
  have hκ1 : -1 ≤ c ^ 2 - s ^ 2 := by nlinarith [sq_nonneg c, sq_nonneg s]
  have hκ2 : c ^ 2 - s ^ 2 ≤ 1 := by nlinarith [sq_nonneg c, sq_nonneg s]
  have hE : ∀ ε : Fin n → Bool, energy w (psi χ M c s ε) =
      Nr n * ((∑ e ∈ M, (w e : ℝ) * ((1 + 2 * c * s) *
        (1 - ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2)) +
        ∑ e ∈ Finset.univ \ M, (w e : ℝ) *
          ((1 - gR M (c ^ 2 - s ^ 2) e.val.1 (ε e.val.1) *
            gR M (c ^ 2 - s ^ 2) e.val.2 (ε e.val.2) *
            ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2)) := by
    intro ε
    rw [energy_eq_pairEnergy, ← Finset.sum_sdiff (Finset.subset_univ M), mul_add,
      Finset.mul_sum, Finset.mul_sum, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun e he => ?_
      rw [psi_matched χ r M c s ε hχ0 hχ1 hχ2 hχ3 hM hcs e he]
      ring
    · refine Finset.sum_congr rfl fun e he => ?_
      rw [psi_cross χ r M c s ε hχ0 hχ1 hχ2 hχ3 hM hcs e (Finset.mem_sdiff.mp he).2]
      ring
  have havg := avg_total n (c ^ 2 - s ^ 2) (Nr n)
    (∑ e ∈ M, (w e : ℝ) * ((1 + 2 * c * s) *
      (1 - ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2))
    (Finset.univ \ M) (fun e => (w e : ℝ))
    (fun e => ∑ a : Fin 3, r e.val.1 a * r e.val.2 a)
    (gR M (c ^ 2 - s ^ 2)) (gR_avg M (c ^ 2 - s ^ 2))
  have hle : ∀ ε : Fin n → Bool, energy w (psi χ M c s ε) ≤ Nr n * optimum ⟨n, w⟩ :=
    fun ε => energy_le_of_norm w _ (Nr n) (Nr_pos n) (psi_sys χ M c s ε hχ0 hM hcs).sqnorm
  have hfin : Nr n * ((∑ e ∈ M, (w e : ℝ) * ((1 + 2 * c * s) *
        (1 - ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2)) +
      (∑ e ∈ Finset.univ \ M, (w e : ℝ) *
        ((1 - (c ^ 2 - s ^ 2) ^ 2 * ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2))) ≤
      Nr n * optimum ⟨n, w⟩ := by
    rw [← havg]
    calc _ = ∑ ε : Fin n → Bool, pW n (c ^ 2 - s ^ 2) ε * energy w (psi χ M c s ε) :=
          Finset.sum_congr rfl fun ε _ => by rw [hE ε]
      _ ≤ ∑ ε : Fin n → Bool, pW n (c ^ 2 - s ^ 2) ε * (Nr n * optimum ⟨n, w⟩) :=
          Finset.sum_le_sum fun ε _ =>
            mul_le_mul_of_nonneg_left (hle ε) (pW_nonneg n _ hκ1 hκ2 ε)
      _ = Nr n * optimum ⟨n, w⟩ := by
          rw [← Finset.sum_mul, pW_sum, one_mul]
  exact le_of_mul_le_mul_left hfin (Nr_pos n)

end QMCPMatch

theorem solution {n : ℕ}
    (w : QuantumMaxCutEnergy.Weights n) (r : Fin n → Fin 3 → ℝ)
    (hr : ∀ i, ∑ a : Fin 3, (r i a) ^ 2 = 1)
    (M : Finset (QuantumMaxCutEnergy.Edge n))
    (hM : ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
      e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2)
    (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (∑ e ∈ M, (w e : ℝ) * ((1 + 2 * c * s) *
        (1 - ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2)) +
      (∑ e ∈ Finset.univ \ M, (w e : ℝ) *
        ((1 - (c ^ 2 - s ^ 2) ^ 2 * ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2)) ≤
      QuantumMaxCutEnergy.optimum ⟨n, w⟩ := by
  exact QMCPMatch.main_bound w r hr M hM c s hcs
