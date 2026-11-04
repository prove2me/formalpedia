-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.coordinateInverse_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:43.248771+00:00
-- url     : https://prove2.me/submissions/0579ef43-5bcf-4e81-9d1c-26b5a5e53579

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Mathlib.Algebra.BigOperators.Finprod
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords


noncomputable section
namespace ThreeSum.TernaryConvolution
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000
private theorem inverse_delta (q a : Fin 3) (C : ℤ) :
    inverseDigit (fun d => (if a=d then 1 else 0)*C) q =
      inverseCoefficient q a*C := by
  fin_cases q <;> fin_cases a <;>
    norm_num [inverseDigit,inverseCoefficient,Nat.choose,Fin.le_def,Fin.ext_iff] <;> ring
end ThreeSum.TernaryConvolution
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryConvolution
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryConvolution
theorem _root_.solution {N : ℕ} (s : Finset (Fin N)) (i : Fin N)
    (hi : i∉s) (A Q : TritWord N) (C : ℤ) :
    coordinateInverse i (fun R => partialKernel s R A*C) Q =
      partialKernel (insert i s) Q A*C := by
  let other : ℤ := ∏ j ∈ (univ : Finset (Fin N)).erase i,
    if j∈s then inverseCoefficient (Q j) (A j) else if A j=Q j then 1 else 0
  have hu (d : Fin 3) : partialKernel s (Function.update Q i d) A =
      (if A i=d then 1 else 0)*other := by
    unfold partialKernel
    rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
    simp only [hi,↓reduceIte,Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp [Function.update_of_ne (mem_erase.mp hj).1]
  have hv : partialKernel (insert i s) Q A = inverseCoefficient (Q i) (A i)*other := by
    unfold partialKernel
    rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
    simp only [mem_insert_self,↓reduceIte]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (mem_erase.mp hj).1
    simp [hji]
  unfold coordinateInverse
  simp_rw [hu,mul_assoc]
  rw [inverse_delta,hv]
  ring
end ThreeSum.TernaryConvolution
