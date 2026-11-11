-- Prove2me | solution 1 for QuantumMaxCutEnergy.PauliSDP.full_level_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:10:49.571803+00:00
-- url     : https://prove2.me/submissions/e1f2958e-7737-44c4-ae05-16a3e175204a

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib
open scoped BigOperators

/-!
Exactness of the Pauli moment relaxation at level `n`.
The first part recalls the physical-state moment embedding; the second part
(`QMCExact`) builds the Pauli operator basis and the sum-of-squares certificate.
-/

noncomputable section

namespace QuantumMaxCutEnergy.Star

def swapWave {n : ℕ} (a b : Fin n) (ψ : Wave n) : Wave n :=
  fun x => ψ (x ∘ Equiv.swap a b)

def edgeAction {n : ℕ} (a b : Fin n) (ψ : Wave n) : Wave n :=
  ψ - swapWave a b ψ

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

end QuantumMaxCutEnergy.Star

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

end QuantumMaxCutEnergy.BaselineSemantic

namespace QuantumMaxCutEnergy

lemma energy_values_bddAbove (G : Input) :
    BddAbove {v : ℝ | ∃ ψ : Wave G.n, squaredNorm ψ = 1 ∧ v = energy G.weights ψ} := by
  refine ⟨2 * totalWeight G.weights, ?_⟩
  rintro v ⟨ψ, hψ, rfl⟩
  simpa [hψ] using energy_upper_bound G.weights ψ

lemma energy_le_optimum (G : Input) (ψ : Wave G.n) (hψ : squaredNorm ψ = 1) :
    energy G.weights ψ ≤ optimum G := by
  exact le_csSup (energy_values_bddAbove G) ⟨ψ, hψ, rfl⟩

end QuantumMaxCutEnergy

namespace QuantumMaxCutEnergy.Star

lemma energy_eq_pairEnergy {n : ℕ} (w : Weights n) (ψ : Wave n) :
    energy w ψ = ∑ e, (w e : ℝ) * pairEnergy e.val.1 e.val.2 ψ := by
  unfold energy
  apply Finset.sum_congr rfl
  intro e he
  rw [pairEnergy_eq]
  ring

end QuantumMaxCutEnergy.Star

open scoped Matrix
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

end AGMRoute.Structural

namespace QuantumMaxCutEnergy.PauliSDP

lemma localProduct_self (a : Label) : localProduct a a = 0 := by
  fin_cases a <;> decide

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

lemma wordProduct_self {n : ℕ} (P : Word n) :
    wordProduct P P = identityWord n := by
  funext i
  exact localProduct_self (P i)

lemma wordProduct_identity_left {n : ℕ} (P : Word n) :
    wordProduct (identityWord n) P = P := by
  funext i
  exact localProduct_identity_left (P i)

lemma wordProduct_identity_right {n : ℕ} (P : Word n) :
    wordProduct P (identityWord n) = P := by
  funext i
  exact localProduct_identity_right (P i)

lemma wordProduct_eq_identity_iff {n : ℕ} (P Q : Word n) :
    wordProduct P Q = identityWord n ↔ P = Q := by
  constructor
  · intro h
    funext i
    exact (localProduct_eq_zero_iff (P i) (Q i)).mp (congrFun h i)
  · rintro rfl
    exact wordProduct_self P

lemma wordPhase_self {n : ℕ} (P : Word n) : wordPhase P P = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  exact localPhase_self (P i)

lemma wordPhase_identity_left {n : ℕ} (P : Word n) :
    wordPhase (identityWord n) P = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  exact localPhase_identity_left (P i)

lemma wordPhase_identity_right {n : ℕ} (P : Word n) :
    wordPhase P (identityWord n) = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  exact localPhase_identity_right (P i)

end QuantumMaxCutEnergy.PauliSDP

open QuantumMaxCutEnergy.PauliSDP

namespace AGMRoute.MomentEmbedding

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
    wordAction (singleWord 1 i) ψ = Structural.pauliX i ψ := by
  funext x
  simp [wordAction, wordAmplitude_single, shiftedBasis_single, Structural.pauliX, flipBit]

theorem wordAction_single_Y {n : ℕ} (i : Fin n) (ψ : Wave n) :
    wordAction (singleWord 2 i) ψ = Structural.pauliY i ψ := by
  funext x
  cases h : x i <;>
    simp [wordAction, wordAmplitude_single, shiftedBasis_single, Structural.pauliY, flipBit, h]

theorem wordAction_single_Z {n : ℕ} (i : Fin n) (ψ : Wave n) :
    wordAction (singleWord 3 i) ψ = Structural.pauliZ i ψ := by
  funext x
  simp only [wordAction, wordAmplitude_single, shiftedBasis_single,
    localFlip_three, Function.update_eq_self]
  cases h : x i <;> simp [Structural.pauliZ, h]

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
      realInner (Structural.pauliX e.val.1 ψ) (Structural.pauliX e.val.2 ψ) := by
  rw [stateMoments, wordAction_twoBody, wordAction_single_X, wordAction_single_X,
    complexInner_re, ← Structural.pauliX_adjoint]

theorem stateMoments_twoBody_Y {n : ℕ} (ψ : Wave n) (e : Edge n) :
    stateMoments ψ (twoBody 2 e) =
      realInner (Structural.pauliY e.val.1 ψ) (Structural.pauliY e.val.2 ψ) := by
  rw [stateMoments, wordAction_twoBody, wordAction_single_Y, wordAction_single_Y,
    complexInner_re, ← Structural.pauliY_adjoint]

theorem stateMoments_twoBody_Z {n : ℕ} (ψ : Wave n) (e : Edge n) :
    stateMoments ψ (twoBody 3 e) =
      realInner (Structural.pauliZ e.val.1 ψ) (Structural.pauliZ e.val.2 ψ) := by
  rw [stateMoments, wordAction_twoBody, wordAction_single_Z, wordAction_single_Z,
    complexInner_re, ← Structural.pauliZ_adjoint]

end AGMRoute.MomentEmbedding

namespace QMCExact

open QuantumMaxCutEnergy QuantumMaxCutEnergy.PauliSDP QuantumMaxCutEnergy.Star
open AGMRoute.Structural AGMRoute.MomentEmbedding
open scoped Matrix ComplexOrder

/-! ### The energy as a combination of Pauli moments, without normalisation -/

theorem energy_moments {n : ℕ} (w : Weights n) (ψ : Wave n) :
    energy w ψ = ∑ e, (w e : ℝ) / 2 * (squaredNorm ψ - stateMoments ψ (twoBody 1 e)
      - stateMoments ψ (twoBody 2 e) - stateMoments ψ (twoBody 3 e)) := by
  rw [energy_eq_pairEnergy]
  apply Finset.sum_congr rfl
  intro e _
  have hij : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  have h := congrArg (Star.realInner ψ) (pauli_sum_swap e.val.1 e.val.2 hij ψ)
  rw [realInner_add_right, realInner_add_right, realInner_add_right,
    realInner_self, ← pauliX_adjoint, ← pauliY_adjoint, ← pauliZ_adjoint,
    realInner_scale_right] at h
  have he : pairEnergy e.val.1 e.val.2 ψ =
      squaredNorm ψ - Star.realInner ψ (swapWave e.val.1 e.val.2 ψ) := by
    simp [pairEnergy, edgeAction, realInner_sub_right, realInner_self]
  rw [stateMoments_twoBody_X, stateMoments_twoBody_Y, stateMoments_twoBody_Z]
  have key : squaredNorm ψ - Star.realInner (pauliX e.val.1 ψ) (pauliX e.val.2 ψ)
      - Star.realInner (pauliY e.val.1 ψ) (pauliY e.val.2 ψ)
      - Star.realInner (pauliZ e.val.1 ψ) (pauliZ e.val.2 ψ) =
      2 * pairEnergy e.val.1 e.val.2 ψ := by linarith
  rw [key]
  ring

theorem energy_scale {n : ℕ} (w : Weights n) (a : ℂ) (ψ : Wave n) :
    energy w (fun x => a * ψ x) = Complex.normSq a * energy w ψ := by
  unfold energy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [← mul_sub, Complex.normSq_mul, ← Finset.mul_sum]
  ring

theorem squaredNorm_scale {n : ℕ} (a : ℂ) (ψ : Wave n) :
    squaredNorm (fun x => a * ψ x) = Complex.normSq a * squaredNorm ψ := by
  simp only [squaredNorm, Complex.normSq_mul, Finset.mul_sum]

theorem energy_le {n : ℕ} (w : Weights n) (ψ : Wave n) :
    energy w ψ ≤ optimum ⟨n, w⟩ * squaredNorm ψ := by
  have hs0 : 0 ≤ squaredNorm ψ := Finset.sum_nonneg fun x _ => Complex.normSq_nonneg _
  rcases hs0.eq_or_lt with h0 | hpos
  · have hz : ∀ x, ψ x = 0 := by
      intro x
      have hx := (Finset.sum_eq_zero_iff_of_nonneg
        (fun x _ => Complex.normSq_nonneg (ψ x))).mp h0.symm x (Finset.mem_univ x)
      exact Complex.normSq_eq_zero.mp hx
    have he : energy w ψ = 0 := by simp [energy, hz]
    rw [he, ← h0, mul_zero]
  · have hsq : 0 < Real.sqrt (squaredNorm ψ) := Real.sqrt_pos.mpr hpos
    have ha : Complex.normSq (((Real.sqrt (squaredNorm ψ))⁻¹ : ℝ) : ℂ) = (squaredNorm ψ)⁻¹ := by
      rw [Complex.normSq_ofReal, ← mul_inv, Real.mul_self_sqrt hs0]
    have h1 : squaredNorm (fun x => (((Real.sqrt (squaredNorm ψ))⁻¹ : ℝ) : ℂ) * ψ x) = 1 := by
      rw [squaredNorm_scale, ha, inv_mul_cancel₀ hpos.ne']
    have h2 : energy w (fun x => (((Real.sqrt (squaredNorm ψ))⁻¹ : ℝ) : ℂ) * ψ x) ≤
        optimum ⟨n, w⟩ := energy_le_optimum ⟨n, w⟩ _ h1
    rw [energy_scale, ha] at h2
    have h3 := mul_le_mul_of_nonneg_right h2 hpos.le
    rwa [mul_comm (squaredNorm ψ)⁻¹, mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one] at h3

/-! ### Pauli matrices -/

def pm {n : ℕ} (P : Word n) : Matrix (Basis n) (Basis n) ℂ :=
  fun x y => if y = shiftedBasis P x then wordAmplitude P x else 0

theorem pm_mulVec {n : ℕ} (P : Word n) (ψ : Wave n) :
    pm P *ᵥ ψ = wordAction P ψ := by
  funext x
  simp [pm, Matrix.mulVec, dotProduct, wordAction]

theorem pm_one (n : ℕ) : pm (identityWord n) = 1 := by
  ext x y
  have hs : shiftedBasis (identityWord n) x = x := by
    funext i
    simp [shiftedBasis, identityWord]
  simp [pm, hs, wordAmplitude, identityWord, Matrix.one_apply, eq_comm]

theorem pm_mul {n : ℕ} (P Q : Word n) :
    pm P * pm Q = wordPhase P Q • pm (wordProduct P Q) := by
  ext x z
  simp only [Matrix.mul_apply, pm, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (shiftedBasis P x)]
  · rw [if_pos rfl, shiftedBasis_product]
    split_ifs
    · exact wordAmplitude_product P Q x
    · simp
  · intro y _ hy
    simp [hy]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem pm_herm {n : ℕ} (P : Word n) : (pm P)ᴴ = pm P := by
  ext x y
  simp only [Matrix.conjTranspose_apply, pm]
  by_cases h : y = shiftedBasis P x
  · subst h
    rw [if_pos (shiftedBasis_twice P x).symm, if_pos rfl, wordAmplitude_conj,
      shiftedBasis_twice]
  · have h' : x ≠ shiftedBasis P y := by
      intro hx
      apply h
      rw [hx, shiftedBasis_twice]
    simp [h, h']

theorem localTrace (a : Label) (ha : a ≠ 0) :
    (∑ b : Bool, if b = localFlip a b then localAmplitude a b else 0) = 0 := by
  fin_cases a <;> simp [localFlip, localAmplitude] at ha ⊢

theorem trace_pm {n : ℕ} (R : Word n) :
    Matrix.trace (pm R) =
      ∏ i, ∑ b : Bool, (if b = localFlip (R i) b then localAmplitude (R i) b else 0) := by
  rw [Fintype.prod_sum]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.prod_ite_zero]
  simp only [Matrix.diag_apply, pm, wordAmplitude, shiftedBasis, funext_iff]
  split_ifs <;> rfl

theorem trace_pm_ne {n : ℕ} (R : Word n) (h : R ≠ identityWord n) :
    Matrix.trace (pm R) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, R i ≠ 0 := by
    by_contra hc
    exact h (funext fun i => by_contra fun hi => hc ⟨i, hi⟩)
  rw [trace_pm]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (localTrace _ hi)

theorem trace_pm_mul {n : ℕ} (P Q : Word n) :
    Matrix.trace (pm P * pm Q) = if P = Q then (Fintype.card (Basis n) : ℂ) else 0 := by
  rw [pm_mul, Matrix.trace_smul]
  split_ifs with h
  · subst h
    rw [wordPhase_self, wordProduct_self, pm_one, Matrix.trace_one, one_smul]
  · rw [trace_pm_ne _ (mt (wordProduct_eq_identity_iff P Q).mp h), smul_zero]

theorem coeff_trace {n : ℕ} (g : Word n → ℂ) (Q : Word n) :
    Matrix.trace (pm Q * ∑ P, g P • pm P) = g Q * (Fintype.card (Basis n) : ℂ) := by
  rw [Matrix.mul_sum, Matrix.trace_sum]
  simp only [Matrix.mul_smul, Matrix.trace_smul, trace_pm_mul, smul_eq_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

theorem card_ne_zero (n : ℕ) : (Fintype.card (Basis n) : ℂ) ≠ 0 := by
  exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Basis n) ≠ 0)

theorem pm_linearIndependent (n : ℕ) :
    LinearIndependent ℂ (pm : Word n → Matrix (Basis n) (Basis n) ℂ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg Q
  have h := coeff_trace g Q
  rw [hg, Matrix.mul_zero, Matrix.trace_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_right (card_ne_zero n)

theorem card_word (n : ℕ) :
    Fintype.card (Word n) = Module.finrank ℂ (Matrix (Basis n) (Basis n) ℂ) := by
  rw [Module.finrank_matrix]
  simp [← mul_pow]

/-- The Pauli words form a basis of the full matrix algebra. -/
def pb (n : ℕ) : Module.Basis (Word n) ℂ (Matrix (Basis n) (Basis n) ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank (pm_linearIndependent n) (card_word n)

theorem pb_apply {n : ℕ} (P : Word n) : pb n P = pm P := by
  simp [pb]

/-! ### The Hamiltonian and its quadratic form -/

def Hm {n : ℕ} (w : Weights n) : Matrix (Basis n) (Basis n) ℂ :=
  ∑ e, (((w e : ℝ) / 2 : ℝ) : ℂ) •
    (1 - pm (twoBody 1 e) - pm (twoBody 2 e) - pm (twoBody 3 e))

theorem quad_pm {n : ℕ} (P : Word n) (ψ : Wave n) :
    star ψ ⬝ᵥ (pm P *ᵥ ψ) = ((stateMoments ψ P : ℝ) : ℂ) := by
  rw [pm_mulVec]
  change complexInner ψ (wordAction P ψ) = _
  apply Complex.ext
  · simp [stateMoments]
  · simp [word_expectation_real]

theorem quad_one {n : ℕ} (ψ : Wave n) :
    star ψ ⬝ᵥ ((1 : Matrix (Basis n) (Basis n) ℂ) *ᵥ ψ) = ((squaredNorm ψ : ℝ) : ℂ) := by
  rw [Matrix.one_mulVec]
  exact complexInner_self ψ

theorem quad_A {n : ℕ} (w : Weights n) (c : ℝ) (ψ : Wave n) :
    star ψ ⬝ᵥ (((c : ℂ) • (1 : Matrix (Basis n) (Basis n) ℂ) - Hm w) *ᵥ ψ) =
      ((c * squaredNorm ψ - energy w ψ : ℝ) : ℂ) := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, quad_one,
    Hm, Matrix.sum_mulVec, dotProduct_sum, energy_moments]
  simp only [Matrix.smul_mulVec, Matrix.sub_mulVec, dotProduct_smul, dotProduct_sub,
    quad_one, quad_pm, smul_eq_mul]
  push_cast
  rfl

theorem A_herm {n : ℕ} (w : Weights n) (c : ℝ) :
    ((c : ℂ) • (1 : Matrix (Basis n) (Basis n) ℂ) - Hm w).IsHermitian := by
  unfold Matrix.IsHermitian Hm
  simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum, pm_herm]

theorem A_psd {n : ℕ} (w : Weights n) :
    (((optimum ⟨n, w⟩ : ℝ) : ℂ) • (1 : Matrix (Basis n) (Basis n) ℂ) - Hm w).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (A_herm w _) (fun ψ => ?_)
  rw [quad_A]
  exact Complex.zero_le_real.mpr (sub_nonneg.mpr (energy_le w ψ))

theorem exists_herm_sqrt {n : ℕ} {A : Matrix (Basis n) (Basis n) ℂ} (hA : A.PosSemidef) :
    ∃ B : Matrix (Basis n) (Basis n) ℂ, Bᴴ = B ∧ B * B = A := by
  open scoped MatrixOrder in
  obtain ⟨X, hX, -, h⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
    (show IsSelfAdjoint A from hA.isHermitian) (QuasispectrumRestricts.nnreal_of_nonneg hA.nonneg)
  exact ⟨X, hX, h⟩

theorem real_coeff {n : ℕ} {B : Matrix (Basis n) (Basis n) ℂ} (hB : Bᴴ = B) :
    ∃ r : Word n → ℝ, B = ∑ P, (r P : ℂ) • pm P := by
  have hsum : ∑ P, (pb n).repr B P • pm P = B := by
    have h := (pb n).sum_repr B
    simpa only [pb_apply] using h
  have hreal : ∀ Q, (((pb n).repr B Q).re : ℂ) = (pb n).repr B Q := by
    intro Q
    have h := coeff_trace (fun P => (pb n).repr B P) Q
    rw [hsum] at h
    have hstar : star (Matrix.trace (pm Q * B)) = Matrix.trace (pm Q * B) := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hB, pm_herm,
        Matrix.trace_mul_comm]
    rw [h, star_mul', star_natCast] at hstar
    exact Complex.conj_eq_iff_re.mp (mul_right_cancel₀ (card_ne_zero n) hstar)
  refine ⟨fun P => ((pb n).repr B P).re, ?_⟩
  calc B = ∑ P, (pb n).repr B P • pm P := hsum.symm
    _ = ∑ P, ((((pb n).repr B P).re : ℝ) : ℂ) • pm P := by simp only [hreal]

/-! ### The main inequality -/

theorem gram_nonneg {n : ℕ} (L : Word n → ℝ) (hL : Feasible n L) (r : Word n → ℝ) :
    0 ≤ ∑ P : Word n, r P * ∑ Q : Word n,
      (wordPhase P Q).re * L (wordProduct P Q) * r Q := by
  have hall : ∀ P : Word n, (support P).card ≤ n := fun P =>
    (Finset.card_le_univ _).trans (by simp)
  have h := hL.2.dotProduct_mulVec_nonneg (fun P : Index n n => r P.val)
  have h' : (∑ P : Word n, r P * ∑ Q : Word n,
      (wordPhase P Q).re * L (wordProduct P Q) * r Q) =
      star (fun P : Index n n => r P.val) ⬝ᵥ
        (realGram n L *ᵥ (fun P : Index n n => r P.val)) := by
    symm
    refine Fintype.sum_equiv (Equiv.subtypeUnivEquiv hall) _ _ (fun P => ?_)
    simp only [Pi.star_apply, star_trivial, Matrix.mulVec, dotProduct, realGram]
    congr 1
    exact Fintype.sum_equiv (Equiv.subtypeUnivEquiv hall) _ _ (fun Q => rfl)
  rw [h']
  exact h

theorem main {n : ℕ} (w : Weights n) (L : Word n → ℝ) (hL : Feasible n L) :
    objective w L ≤ optimum ⟨n, w⟩ := by
  obtain ⟨B, hB, hBB⟩ := exists_herm_sqrt (A_psd w)
  obtain ⟨r, hr⟩ := real_coeff hB
  have hℓ : ∀ R, (pb n).constr ℂ (fun R => (L R : ℂ)) (pm R) = (L R : ℂ) := by
    intro R
    rw [← pb_apply R]
    exact (pb n).constr_basis ℂ _ R
  have h1 : (pb n).constr ℂ (fun R => (L R : ℂ)) (B * B) =
      ∑ P, ∑ Q, ((r P : ℂ) * (r Q : ℂ)) * (wordPhase P Q * (L (wordProduct P Q) : ℂ)) := by
    rw [hr, Finset.sum_mul]
    simp only [Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, pm_mul, map_sum, map_smul,
      hℓ, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro P _
    apply Finset.sum_congr rfl
    intro Q _
    ring
  have h2 : (pb n).constr ℂ (fun R => (L R : ℂ))
      (((optimum ⟨n, w⟩ : ℝ) : ℂ) • (1 : Matrix (Basis n) (Basis n) ℂ) - Hm w) =
      ((optimum ⟨n, w⟩ - objective w L : ℝ) : ℂ) := by
    rw [Hm, ← pm_one]
    simp only [map_sub, map_sum, map_smul, hℓ, smul_eq_mul, hL.1, objective]
    push_cast
    rw [mul_one, sub_right_inj]
    apply Finset.sum_congr rfl
    intro e _
    ring
  have h3 := gram_nonneg L hL r
  rw [hBB, h2] at h1
  have h4 := congrArg Complex.re h1
  rw [Complex.ofReal_re, Complex.re_sum] at h4
  have h5 : ∀ P : Word n, (∑ Q, ((r P : ℂ) * (r Q : ℂ)) *
      (wordPhase P Q * (L (wordProduct P Q) : ℂ))).re =
      r P * ∑ Q, (wordPhase P Q).re * L (wordProduct P Q) * r Q := by
    intro P
    rw [Complex.re_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Q _
    rw [← Complex.ofReal_mul, Complex.re_ofReal_mul, Complex.re_mul_ofReal]
    ring
  simp only [h5] at h4
  linarith

end QMCExact

end

theorem solution {n : ℕ}
    (w : QuantumMaxCutEnergy.Weights n)
    (L : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ)
    (hL : QuantumMaxCutEnergy.PauliSDP.Feasible n L) :
    QuantumMaxCutEnergy.PauliSDP.objective w L ≤ QuantumMaxCutEnergy.optimum ⟨n, w⟩ := by
  exact QMCExact.main w L hL
