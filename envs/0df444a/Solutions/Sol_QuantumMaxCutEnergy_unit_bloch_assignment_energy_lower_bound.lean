-- Prove2me | solution 1 for QuantumMaxCutEnergy.unit_bloch_assignment_energy_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T16:01:33.660415+00:00
-- url     : https://prove2.me/submissions/72364d10-947f-434c-86e5-818b8e33ddde

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel

-- Local proof source: AGMBlochWaveFoundation

/-! Private finite-wave helpers extracted from the previously checked
QMC analytic proofs, with narrow imports and separate helper names. -/
noncomputable section
open scoped BigOperators
open QuantumMaxCutEnergy
namespace AGMRoute.BlochFoundation

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


end AGMRoute.BlochFoundation

open AGMRoute.BlochFoundation
namespace AGMRoute.BlochStructural

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

end AGMRoute.BlochStructural


-- Local proof source: AGMBlochPauliOps

/-! Bloch-only finite Pauli operator helpers, extracted from the checked
physical-embedding proof. No public definition is modified or redefined.
The local tables and actions are private proof auxiliaries. -/

noncomputable section
open scoped BigOperators Matrix
open QuantumMaxCutEnergy AGMRoute.BlochFoundation
namespace AGMRoute.BlochOps

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



end AGMRoute.BlochOps


-- Local proof source: AGMBlochTensorCore

/-!
Actual pure product-state witnesses for rank-three Bloch vectors.
Sources: GP19 Bloch-vector representation and product energy formula;
AGM20 Eq. (6). This is an analytic existence proof, not state preparation.
-/

noncomputable section
open scoped BigOperators Matrix
open QuantumMaxCutEnergy AGMRoute.BlochFoundation
open AGMRoute.BlochOps
open AGMRoute.BlochOps

namespace AGMRoute.Bloch

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


end AGMRoute.Bloch


-- Local proof source: AGMBlochProductState

noncomputable section
open scoped BigOperators Matrix
open QuantumMaxCutEnergy AGMRoute.BlochFoundation
open AGMRoute.BlochOps
namespace AGMRoute.Bloch

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


end AGMRoute.Bloch


-- Local proof source: AGMBlochEnergyWitness

noncomputable section
open scoped BigOperators
open QuantumMaxCutEnergy AGMRoute.BlochFoundation
open AGMRoute.BlochOps AGMRoute.Bloch

namespace AGMRoute.Bloch

theorem productWave_twoBody_moment {n : ℕ} (φ : Fin n → Bool → ℂ)
    (hφ : ∀ i, Complex.normSq (φ i false) + Complex.normSq (φ i true) = 1)
    (a : Label) (r : Fin n → ℝ)
    (ha : ∀ i, localExpectation (φ i) a = (r i : ℂ)) (e : Edge n) :
    stateMoments (productWave φ) (twoBody a e) = r e.val.1 * r e.val.2 := by
  unfold stateMoments
  rw [productWave_word_expectation]
  have hij : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  have hterm (i : Fin n) : localExpectation (φ i) (twoBody a e i) =
      (if i = e.val.1 then (r e.val.1 : ℂ) else 1) *
        (if i = e.val.2 then (r e.val.2 : ℂ) else 1) := by
    by_cases hi : i = e.val.1
    · subst i
      simp [twoBody, hij, ha]
    · by_cases hj : i = e.val.2
      · subst i
        simp [twoBody, Ne.symm hij, ha]
      · simp [twoBody, hi, hj, localExpectation_identity (φ i) (hφ i)]
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib]
  simp

theorem product_state_energy_witness {n : ℕ} (w : Weights n)
    (r : Fin n → Fin 3 → ℝ) (hr : ∀ i, (∑ a : Fin 3, (r i a) ^ 2) = 1) :
    ∃ ψ : Wave n, squaredNorm ψ = 1 ∧
      energy w ψ = ∑ e : Edge n, (w e : ℝ) *
        (1 - ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2 := by
  have hlocal (i : Fin n) := qubit_of_unit_bloch (r i 0) (r i 1) (r i 2)
    (by simpa only [Fin.sum_univ_three] using hr i)
  let φ (i : Fin n) : Bool → ℂ := Classical.choose (hlocal i)
  have hspec (i : Fin n) := Classical.choose_spec (hlocal i)
  have hφ (i : Fin n) : Complex.normSq (φ i false) + Complex.normSq (φ i true) = 1 :=
    (hspec i).1
  have hX (e : Edge n) : stateMoments (productWave φ) (twoBody 1 e) =
      r e.val.1 0 * r e.val.2 0 :=
    productWave_twoBody_moment φ hφ 1 (fun i => r i 0) (fun i => (hspec i).2.1) e
  have hY (e : Edge n) : stateMoments (productWave φ) (twoBody 2 e) =
      r e.val.1 1 * r e.val.2 1 :=
    productWave_twoBody_moment φ hφ 2 (fun i => r i 1) (fun i => (hspec i).2.2.1) e
  have hZ (e : Edge n) : stateMoments (productWave φ) (twoBody 3 e) =
      r e.val.1 2 * r e.val.2 2 :=
    productWave_twoBody_moment φ hφ 3 (fun i => r i 2) (fun i => (hspec i).2.2.2) e
  have hnorm := productWave_norm φ hφ
  refine ⟨productWave φ, hnorm, ?_⟩
  rw [← stateMoments_objective w (productWave φ) hnorm]
  unfold objective
  apply Finset.sum_congr rfl
  intro e _
  rw [hX e, hY e, hZ e, Fin.sum_univ_three]
  ring

theorem solution (G : Input) (r : Fin G.n → Fin 3 → ℝ)
    (hr : ∀ i, (∑ a : Fin 3, (r i a) ^ 2) = 1) :
    (∑ e : Edge G.n, (G.weights e : ℝ) *
      (1 - ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2) ≤ optimum G := by
  obtain ⟨ψ, hψ, henergy⟩ := product_state_energy_witness G.weights r hr
  rw [← henergy]
  exact energy_le_optimum G ψ hψ


end AGMRoute.Bloch


theorem solution (G : QuantumMaxCutEnergy.Input) (r : Fin G.n → Fin 3 → ℝ)
    (hr : ∀ i, (∑ a : Fin 3, (r i a) ^ 2) = 1) :
    (∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) *
      (1 - ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2) ≤ QuantumMaxCutEnergy.optimum G := by
  exact AGMRoute.Bloch.solution G r hr

#print axioms solution
