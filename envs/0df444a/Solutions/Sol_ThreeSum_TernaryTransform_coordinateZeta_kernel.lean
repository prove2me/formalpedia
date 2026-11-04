-- Prove2me | solution 1 for ThreeSum.TernaryTransform.coordinateZeta_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:20:38.70312+00:00
-- url     : https://prove2.me/submissions/3cb9b22c-9de6-4713-b86a-941800bbcd37

import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords


noncomputable section
namespace ThreeSum.TernaryTransform
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryEuler
private theorem zeta_delta (q a : Fin 3) (C : ℤ) :
    zetaDigit (fun d => (if a = d then 1 else 0) * C) q = digitChoose q a * C := by
  fin_cases q <;> fin_cases a <;>
    norm_num [zetaDigit, digitChoose, Nat.choose, Fin.ext_iff] <;> ring
end ThreeSum.TernaryTransform
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTransform
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryEuler
namespace ThreeSum.TernaryTransform
theorem _root_.solution {N : ℕ} (s : Finset (Fin N)) (i : Fin N)
    (hi : i ∉ s) (A R : TritWord N) (C : ℤ) :
    coordinateZeta i (fun Q => kernel s Q A * C) R = kernel (insert i s) R A * C := by
  let other : ℤ := ∏ j ∈ (univ : Finset (Fin N)).erase i,
    if j ∈ s then digitChoose (R j) (A j) else if A j = R j then 1 else 0
  have hu (d : Fin 3) : kernel s (Function.update R i d) A =
      (if A i = d then 1 else 0) * other := by
    unfold kernel
    rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
    simp only [hi, ↓reduceIte, Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp [Function.update_of_ne (mem_erase.mp hj).1]
  have hv : kernel (insert i s) R A = digitChoose (R i) (A i) * other := by
    unfold kernel
    rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
    simp only [mem_insert_self, ↓reduceIte]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (mem_erase.mp hj).1
    simp [hji]
  unfold coordinateZeta
  simp_rw [hu, mul_assoc]
  rw [zeta_delta, hv]
  ring
end ThreeSum.TernaryTransform
