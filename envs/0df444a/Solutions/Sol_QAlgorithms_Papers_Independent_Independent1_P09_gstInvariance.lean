-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P09.gstInvariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:49:50.007147+00:00
-- url     : https://prove2.me/submissions/93cc7885-ed61-440c-ab81-0085323aeec0

import Definitions.Def_QAlgorithms_Defs_MitigationTrials
import Definitions.Def_QAlgorithms_Defs_MitigationTomography
import Definitions.Def_QAlgorithms_Defs_MitigationDecompositions
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P09_Model
import Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P09_pauliTransferIdentities
set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexOrder NNReal ENNReal
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
namespace QAlgorithms.Papers.Independent.Independent1.P09
open ErrorMitigation

lemma S173M_entry {ι : Type*} [Fintype ι] (X Y Z : Matrix ι ι ℝ) (a b : ι) :
    X a ⬝ᵥ (Y *ᵥ fun i => Z i b) = (X * Y * Z) a b := by
  simp only [dotProduct, Matrix.mulVec, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

lemma S173M_conj_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (S S' : Matrix ι ι ℝ) (h : S' * S = 1)
    (h2 : S * S' = 1) (L : List (Matrix ι ι ℝ)) : (L.map (fun M => S * M * S')).prod = S * L.prod * S' := by
  induction L with
  | nil => simp [h2]
  | cons M L ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    calc S * M * S' * (S * L.prod * S') = S * M * (S' * S) * L.prod * S' := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]

lemma S173M_obs_herm {n : ℕ} (M : ObservableMeasurement (Qubits n)) : M.observable.IsHermitian := by
  unfold ObservableMeasurement.observable Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  have h := (M.valid.1 o).1
  unfold Matrix.IsHermitian at h
  rw [Matrix.conjTranspose_smul, h]; simp

theorem S173M_main {n t : ℕ} (F : TomographicFrame n)
    (hin : IsUnit F.inputMatrix) (hout : IsUnit F.outputMatrix)
    (T : Matrix (PauliIndex n) (PauliIndex n) ℝ) (hT : IsUnit T)
    (O : Fin t → Matrix (Qubits n) (Qubits n) ℂ →ₗ[ℂ]
      Matrix (Qubits n) (Qubits n) ℂ)
    (kraus : ∀ j, ∃ r : ℕ, ∃ K : Fin r → Matrix (Qubits n) (Qubits n) ℂ,
      O j = krausLinearMap K) :
    let g := F.gram
    let data := fun j => Matrix.of fun a b =>
      ((F.measurement a).observable * O j (F.preparation b)).trace.re
    let hat := fun j => T*g⁻¹*data j*T⁻¹
    IsUnit g ∧
    (∀ j, data j = F.outputMatrix*pauliTransferMatrix (O j)*F.inputMatrix ∧
      hat j = T*F.inputMatrix⁻¹*pauliTransferMatrix (O j)*F.inputMatrix*T⁻¹) ∧
    ∀ a b, ((F.measurement a).observable *
      ((List.ofFn O).foldl (fun X op => op X) (F.preparation b))).trace.re =
        (g*T⁻¹) a ⬝ᵥ (((List.ofFn hat).reverse.prod).mulVec (fun i => T i b)) := by
  intro g data hat
  choose r K hK using kraus
  have hOK : O = fun j => krausLinearMap (K j) := funext hK
  set Iin := F.inputMatrix
  set Iout := F.outputMatrix
  have hin' : Iin⁻¹ * Iin = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hin)
  have hin'' : Iin * Iin⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hin)
  have hout' : Iout⁻¹ * Iout = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hout)
  have hT' : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hT)
  have hginv : g⁻¹ = Iin⁻¹ * Iout⁻¹ := by
    show (Iout * Iin)⁻¹ = _
    rw [Matrix.mul_inv_rev]
  have hdata : ∀ j, data j = Iout * pauliTransferMatrix (O j) * Iin := by
    intro j
    ext a b
    have h := (pauliTransferIdentities (t := 1) (F.preparation b) (F.measurement a).observable
      (F.density b) (S173M_obs_herm _) (fun _ => r j) (fun _ => K j)).2
    simp only [List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, Matrix.mul_one] at h
    simp only [data, Matrix.of_apply]
    rw [hK j, h]
    exact S173M_entry Iout (pauliTransferMatrix (krausLinearMap (K j))) Iin a b
  have hhat : ∀ j, hat j = T * Iin⁻¹ * pauliTransferMatrix (O j) * Iin * T⁻¹ := by
    intro j
    show T * g⁻¹ * data j * T⁻¹ = _
    rw [hdata j, hginv]
    calc T * (Iin⁻¹ * Iout⁻¹) * (Iout * pauliTransferMatrix (O j) * Iin) * T⁻¹
        = T * Iin⁻¹ * (Iout⁻¹ * Iout) * pauliTransferMatrix (O j) * Iin * T⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hout', Matrix.mul_one]
  refine ⟨hout.mul hin, fun j => ⟨hdata j, hhat j⟩, ?_⟩
  intro a b
  set S := T * Iin⁻¹
  set S' := Iin * T⁻¹
  have hSS : S' * S = 1 := by
    calc Iin * T⁻¹ * (T * Iin⁻¹) = Iin * (T⁻¹ * T) * Iin⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hT', Matrix.mul_one, hin'']
  have hT'' : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hT)
  have hSS' : S * S' = 1 := by
    calc T * Iin⁻¹ * (Iin * T⁻¹) = T * (Iin⁻¹ * Iin) * T⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hin', Matrix.mul_one, hT'']
  set PT := List.ofFn fun j => pauliTransferMatrix (O j)
  have hlist : (List.ofFn hat).reverse = PT.reverse.map (fun M => S * M * S') := by
    rw [List.map_reverse, List.map_ofFn]
    apply congrArg List.reverse
    apply congrArg List.ofFn
    funext j
    simp only [Function.comp_apply, hhat j, S, S', Matrix.mul_assoc]
  have hprod : ((List.ofFn hat).reverse.prod) = S * PT.reverse.prod * S' := by
    rw [hlist]
    exact S173M_conj_prod S S' hSS hSS' PT.reverse
  have hfin := (pauliTransferIdentities (F.preparation b) (F.measurement a).observable
      (F.density b) (S173M_obs_herm _) r K).2
  simp only [← hK] at hfin
  rw [hfin, hprod, S173M_entry (g * T⁻¹)]
  refine Eq.trans (S173M_entry Iout PT.reverse.prod Iin a b) ?_
  have hg : g = Iout * Iin := rfl
  rw [hg]
  congr 1
  simp only [S, S', Matrix.mul_assoc]
  rw [← Matrix.mul_assoc T⁻¹ T, hT', Matrix.one_mul, ← Matrix.mul_assoc Iin Iin⁻¹, hin'', Matrix.one_mul]
  simp only [← Matrix.mul_assoc, Matrix.mul_one]

end QAlgorithms.Papers.Independent.Independent1.P09

open QAlgorithms QAlgorithms.Papers.Independent.Independent1.P09
open ErrorMitigation in
theorem solution {n t : ℕ} (F : TomographicFrame n)
    (hin : IsUnit F.inputMatrix) (hout : IsUnit F.outputMatrix)
    (T : Matrix (PauliIndex n) (PauliIndex n) ℝ) (hT : IsUnit T)
    (O : Fin t → Matrix (Qubits n) (Qubits n) ℂ →ₗ[ℂ]
      Matrix (Qubits n) (Qubits n) ℂ)
    (kraus : ∀ j, ∃ r : ℕ, ∃ K : Fin r → Matrix (Qubits n) (Qubits n) ℂ,
      O j = krausLinearMap K) :
    let g := F.gram
    let data := fun j => Matrix.of fun a b =>
      ((F.measurement a).observable * O j (F.preparation b)).trace.re
    let hat := fun j => T*g⁻¹*data j*T⁻¹
    IsUnit g ∧
    (∀ j, data j = F.outputMatrix*pauliTransferMatrix (O j)*F.inputMatrix ∧
      hat j = T*F.inputMatrix⁻¹*pauliTransferMatrix (O j)*F.inputMatrix*T⁻¹) ∧
    ∀ a b, ((F.measurement a).observable *
      ((List.ofFn O).foldl (fun X op => op X) (F.preparation b))).trace.re =
        (g*T⁻¹) a ⬝ᵥ (((List.ofFn hat).reverse.prod).mulVec (fun i => T i b)) :=
  S173M_main F hin hout T hT O kraus
