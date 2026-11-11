-- Prove2me | solution 1 for PauliUnclonable531.Pauli.decryption_execution
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T09:44:46.009437+00:00
-- url     : https://prove2.me/submissions/00063cc6-1bf9-49eb-a198-330c3ff80fcc

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Instructions

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli.Kit


open PauliUnclonable531.Pauli

/-- The tensor product `⊗ᵢ fᵢ` of single-qubit matrices, on the computational basis. -/
def tens {n : ℕ} (f : Fin n → Op (Fin 2)) : Op (Bits n) := fun x y => ∏ i, f i (x i) (y i)

lemma tens_mul {n : ℕ} (f g : Fin n → Op (Fin 2)) :
    tens f * tens g = tens (fun i => f i * g i) := by
  ext x y
  simp only [tens, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp [Finset.prod_mul_distrib]

lemma tens_one {n : ℕ} : tens (fun _ : Fin n => (1 : Op (Fin 2))) = 1 := by
  ext x y
  simp only [tens, Matrix.one_apply]
  rw [Finset.prod_boole]
  simp [funext_iff]

lemma tens_smul {n : ℕ} (c : Fin n → ℂ) (f : Fin n → Op (Fin 2)) :
    tens (fun i => c i • f i) = (∏ i, c i) • tens f := by
  ext x y
  simp [tens, Finset.prod_mul_distrib]

lemma tens_conjTranspose {n : ℕ} (f : Fin n → Op (Fin 2)) :
    (tens f).conjTranspose = tens (fun i => (f i).conjTranspose) := by
  ext x y
  simp [tens, star_prod]

lemma tens_transpose {n : ℕ} (f : Fin n → Op (Fin 2)) :
    (tens f).transpose = tens (fun i => (f i).transpose) := by
  ext x y
  simp [tens]

lemma tens_trace {n : ℕ} (f : Fin n → Op (Fin 2)) :
    (tens f).trace = ∏ i, (f i).trace := by
  simp only [Matrix.trace, Matrix.diag, tens]
  rw [Fintype.prod_sum]

lemma pauli_eq_tens {n : ℕ} (k : Label n) :
    pauli k = tens (fun j => QMaxCutSDP.Rounding.pauli (localLabel (k.1 j) (k.2 j))) := rfl

lemma sign_add (a b : Fin 2) : sign (a + b) = sign a * sign b := by
  fin_cases a <;> fin_cases b <;> simp [sign]

lemma sign_sum {ι : Type} (s : Finset ι) (f : ι → Fin 2) :
    sign (∑ i ∈ s, f i) = ∏ i ∈ s, sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sign]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sign_add, ih]


/-! ## Local operators -/

lemma onWire_eq_tens {n : ℕ} (j : Fin n) (M : Op (Fin 2)) :
    onWire j M = tens (fun i => if i = j then M else 1) := by
  ext x y
  simp only [onWire, tens]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> simp [Matrix.one_apply, *]

lemma onWire_apply {n : ℕ} (j : Fin n) (M : Op (Fin 2)) (x y : Bits n) :
    onWire j M x y = M (x j) (y j) * ∏ i ∈ Finset.univ.erase j, (if x i = y i then 1 else 0) := by
  unfold onWire
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), if_pos rfl]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [if_neg (Finset.ne_of_mem_erase hi)]

lemma onWire_one {n : ℕ} (j : Fin n) : onWire j (1 : Op (Fin 2)) = 1 := by
  rw [onWire_eq_tens]
  simpa using tens_one

lemma onWire_affine {n : ℕ} (j : Fin n) (c s : ℂ) (M : Op (Fin 2)) :
    onWire j (c • (1 + s • M)) = c • (1 + s • onWire j M) := by
  have h1 : (1 : Op (Bits n)) = onWire j 1 := (onWire_one j).symm
  rw [h1]
  ext x y
  simp only [onWire_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

lemma onWire_mul {n : ℕ} (j : Fin n) (A B : Op (Fin 2)) :
    onWire j A * onWire j B = onWire j (A * B) := by
  rw [onWire_eq_tens, onWire_eq_tens, onWire_eq_tens, tens_mul]
  congr 1
  funext i
  split_ifs <;> simp

lemma onWire_comm {n : ℕ} {j j' : Fin n} (h : j ≠ j') (A B : Op (Fin 2)) :
    onWire j A * onWire j' B = onWire j' B * onWire j A := by
  rw [onWire_eq_tens, onWire_eq_tens, tens_mul, tens_mul]
  congr 1
  funext i
  by_cases hi : i = j
  · subst hi; simp [h]
  · by_cases hi' : i = j' <;> simp [hi, hi', Ne.symm h]

lemma onWire_conjTranspose {n : ℕ} (j : Fin n) (A : Op (Fin 2)) :
    (onWire j A).conjTranspose = onWire j A.conjTranspose := by
  rw [onWire_eq_tens, onWire_eq_tens, tens_conjTranspose]
  congr 1
  funext i
  split_ifs <;> simp

lemma qubit_sq (a : Fin 4) : QMaxCutSDP.Rounding.pauli a * QMaxCutSDP.Rounding.pauli a = 1 := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [QMaxCutSDP.Rounding.pauli, Matrix.mul_apply, Fin.sum_univ_two]

lemma qubit_herm (a : Fin 4) :
    (QMaxCutSDP.Rounding.pauli a).conjTranspose = QMaxCutSDP.Rounding.pauli a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [QMaxCutSDP.Rounding.pauli]

/-! ## Sequential measurement -/

/-- The local observable measured by an instruction. -/
noncomputable def obs {n : ℕ} (i : DecInstruction n) : Op (Bits n) :=
  onWire i.wire (QMaxCutSDP.Rounding.pauli i.label)

noncomputable def prodObs {n : ℕ} (L : List (DecInstruction n)) : Op (Bits n) :=
  (L.map obs).prod

/-- Two-outcome effect on the parity of `L`'s outcomes. -/
noncomputable def parityEffect {n : ℕ} (L : List (DecInstruction n)) (c : Fin 2) : Op (Bits n) :=
  (1/2 : ℂ) • (1 + sign c • prodObs L)

lemma obs_sq {n : ℕ} (i : DecInstruction n) : obs i * obs i = 1 := by
  rw [obs, onWire_mul, qubit_sq, onWire_one]

lemma obs_herm {n : ℕ} (i : DecInstruction n) : (obs i).conjTranspose = obs i := by
  rw [obs, onWire_conjTranspose, qubit_herm]

lemma localProjector_eq {n : ℕ} (i : DecInstruction n) (b : Fin 2) :
    localProjector i b = (1/2 : ℂ) • (1 + sign b • obs i) := by
  rw [localProjector, onWire_affine]; rfl

lemma obs_comm_prod {n : ℕ} (i : DecInstruction n) (L : List (DecInstruction n))
    (h : ∀ i' ∈ L, i'.wire ≠ i.wire) : obs i * prodObs L = prodObs L * obs i := by
  induction L with
  | nil => simp [prodObs]
  | cons a L ih =>
    simp only [prodObs, List.map_cons, List.prod_cons] at ih ⊢
    have ha : obs i * obs a = obs a * obs i :=
      onWire_comm (h a List.mem_cons_self).symm _ _
    rw [← Matrix.mul_assoc, ha, Matrix.mul_assoc, ih (fun i' hi' => h i' (List.mem_cons_of_mem _ hi')),
      Matrix.mul_assoc]

lemma sign_sub (a b : Fin 2) : sign (a - b) = sign a * sign b := by
  fin_cases a <;> fin_cases b <;> simp [sign]

lemma sign_sq (b : Fin 2) : sign b * sign b = 1 := by
  fin_cases b <;> simp [sign]

lemma born_trace_cycle {n : ℕ} (E P σ : Op (Bits n)) :
    born E (P * σ * P.conjTranspose) = born (P.conjTranspose * E * P) σ := by
  unfold born
  congr 1
  calc (E * (P * σ * P.conjTranspose)).trace = ((E * P * σ) * P.conjTranspose).trace := by
        simp only [Matrix.mul_assoc]
    _ = (P.conjTranspose * (E * P * σ)).trace := Matrix.trace_mul_comm _ _
    _ = (P.conjTranspose * E * P * σ).trace := by simp only [Matrix.mul_assoc]

lemma born_add' {n : ℕ} (Q Q' ρ : Op (Bits n)) : born (Q + Q') ρ = born Q ρ + born Q' ρ := by
  simp [born, Matrix.add_mul, Matrix.trace_add]

/-- One measurement step of the parity computation, as an operator identity. -/
lemma step_identity {n : ℕ} (i : DecInstruction n) (L : List (DecInstruction n))
    (h : ∀ i' ∈ L, i'.wire ≠ i.wire) (c : Fin 2) :
    (∑ b : Fin 2, (localProjector i b).conjTranspose * parityEffect L (c - b) * localProjector i b) =
      parityEffect (i :: L) c := by
  have hOR := obs_comm_prod i L h
  have hOO := obs_sq i
  have hPh : ∀ b, (localProjector i b).conjTranspose = localProjector i b := by
    intro b
    rw [localProjector_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one, obs_herm]
    fin_cases b <;> simp [sign]
  have hcomm : ∀ b d : Fin 2, localProjector i b * parityEffect L d =
      parityEffect L d * localProjector i b := by
    intro b d
    rw [localProjector_eq, parityEffect]
    simp only [Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, one_mul, mul_one,
      smul_mul_assoc, mul_smul_comm]
    rw [hOR]
    module
  have hidem : ∀ b : Fin 2, localProjector i b * localProjector i b = localProjector i b := by
    intro b
    rw [localProjector_eq]
    simp only [Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, one_mul, mul_one,
      smul_mul_assoc, mul_smul_comm, smul_smul, hOO]
    have := sign_sq b
    fin_cases b <;> simp [sign] at this ⊢ <;> module
  have hterm : ∀ b : Fin 2, (localProjector i b).conjTranspose * parityEffect L (c - b) *
      localProjector i b = localProjector i b * parityEffect L (c - b) := by
    intro b
    rw [hPh, Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc, hidem]
  simp only [hterm]
  simp only [localProjector_eq, parityEffect, prodObs, List.map_cons, List.prod_cons]
  simp only [sign_sub]
  simp only [Fin.sum_univ_two, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, one_mul,
    mul_one, smul_mul_assoc, mul_smul_comm, smul_smul]
  fin_cases c <;> simp [sign] <;> module

lemma execute_eq {n : ℕ} (L : List (DecInstruction n)) (hL : (L.map DecInstruction.wire).Nodup)
    (σ : Op (Bits n)) (par t : Fin 2) :
    executeDec L σ par t = born (parityEffect L (t - par)) σ := by
  induction L generalizing σ par with
  | nil =>
    simp only [executeDec, parityEffect, prodObs, List.map_nil, List.prod_nil]
    fin_cases par <;> fin_cases t <;> simp [born, sign, Matrix.trace_smul, ← add_smul] <;> norm_num
  | cons i L ih =>
    rw [List.map_cons, List.nodup_cons] at hL
    have hw : ∀ i' ∈ L, i'.wire ≠ i.wire := by
      intro i' hi' heq
      exact hL.1 (heq ▸ List.mem_map_of_mem hi')
    simp only [executeDec]
    simp only [ih hL.2, born_trace_cycle]
    rw [← step_identity i L hw (t - par), Fin.sum_univ_two, Fin.sum_univ_two, born_add']
    congr 3 <;> rw [sub_sub]

lemma prod_onWire {n : ℕ} (f : Fin n → Op (Fin 2)) (L : List (Fin n)) (hL : L.Nodup) :
    (L.map fun j => onWire j (f j)).prod = tens (fun i => if i ∈ L then f i else 1) := by
  induction L with
  | nil => simpa using tens_one.symm
  | cons a L ih =>
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, ih hL.2, onWire_eq_tens, tens_mul]
    congr 1
    funext i
    by_cases hi : i = a
    · subst hi; simp [hL.1]
    · simp [hi]

lemma prodObs_decProgram {n : ℕ} (k : Key n) : prodObs (decProgram k) = pauli k.val := by
  rw [prodObs, decProgram, List.map_map]
  have := prod_onWire (fun j => QMaxCutSDP.Rounding.pauli (localLabel (k.val.1 j) (k.val.2 j)))
    ((List.finRange n).filter (active k.val)) ((List.nodup_finRange n).filter _)
  refine this.trans ?_
  rw [pauli_eq_tens]
  congr 1
  funext i
  by_cases hi : active k.val i = true
  · simp [hi]
  · have h0 : k.val.1 i = 0 ∧ k.val.2 i = 0 := by
      simpa [active] using hi
    simp [hi, h0.1, h0.2, localLabel, QMaxCutSDP.Rounding.pauli]
    ext a b; fin_cases a <;> fin_cases b <;> rfl

end PauliUnclonable531.Pauli.Kit

open PauliUnclonable531.Pauli PauliUnclonable531.Pauli.Kit in
theorem solution (n : ℕ) (k : Key n) (σ : Op (Bits n)) (b : Fin 2) :
    operationalDec k σ b = born (decryptEffect k b) σ := by
  have hnodup : ((decProgram k).map DecInstruction.wire).Nodup := by
    rw [decProgram, List.map_map]
    have : (DecInstruction.wire ∘ fun j : Fin n =>
        (⟨j, localLabel (k.val.1 j) (k.val.2 j)⟩ : DecInstruction n)) = id := rfl
    rw [this, List.map_id]
    exact (List.nodup_finRange n).filter _
  rw [operationalDec, execute_eq _ hnodup, sub_zero, parityEffect, prodObs_decProgram]
  rfl
