-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.boundaryColumnWeight_inr_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:47:34.260596+00:00
-- url     : https://prove2.me/submissions/b66dd740-b6ef-4917-8a67-550f13eb6b75

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Theorems.Thm_QEC_Coding_DistanceBalancing_matrixToLin_single
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_fixed_base_coordinate_eq
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_one_fiber_coordinate_eq
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_sum_elim_eq
import Theorems.Thm_QEC_Coding_FiberBundle_wordLinearMapTranspose_matrixToLin_single

section
namespace QEC.Coding.DistanceBalancing
universe u
open QEC.Coding.FiberBundle
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)
private theorem HammingWeight_reverse_fiber_coordinate_eq
    {B I : Type u} [Fintype B] [Fintype I] [DecidableEq I]
    (x : Word (ZMod 2) B) (i : I) :
    HammingWeight (fun p : B × I ↦ if p.2 = i then x p.1 else 0) =
      HammingWeight x := by
  -- Swap the condition pointwise before transporting it through HammingWeight.
  have hswap : (fun p : B × I ↦ if p.2 = i then x p.1 else 0) =
      (fun p : B × I ↦ if i = p.2 then x p.1 else 0) := by
    funext p
    by_cases hpi : p.2 = i
    · rw [if_pos hpi, if_pos hpi.symm]
    · rw [if_neg hpi, if_neg (Ne.symm hpi)]
  rw [hswap]
  exact HammingWeight_one_fiber_coordinate_eq x (fun _ ↦ Equiv.refl I) i
end QEC.Coding.DistanceBalancing
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open QEC.Coding.FiberBundle
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)
namespace QEC.Coding.DistanceBalancing
theorem _root_.solution
    (x2 : xTwo) (b : classicalCheck) :
    HammingWeight (boundary1 D (Pi.single (Sum.inr (x2, b)) 1)) +
        HammingWeight
          (wordLinearMapTranspose (boundary2 D)
            (Pi.single (Sum.inr (x2, b)) 1)) =
      HammingWeight (fun x1 ↦ D.xBoundary2 x1 x2) +
        HammingWeight (fun a ↦ D.classicalBoundary b a) := by
  rw [boundary1, matrixToLin_single]
  rw [boundary2, wordLinearMapTranspose_matrixToLin_single]
  have hWord1 :
      (fun r ↦ boundary1Matrix D r (Sum.inr (x2, b))) =
        (Sum.elim
          (fun _ : xZero × classicalBit ↦ 0)
          (fun p : xOne × classicalCheck ↦
            if p.2 = b then D.xBoundary2 p.1 x2 else 0)) := by
    funext r
    cases r <;> rfl
  have hWord2 :
      (fun c ↦ boundary2Matrix D (Sum.inr (x2, b)) c) =
        (fun p : xTwo × classicalBit ↦
          if x2 = p.1 then D.classicalBoundary b p.2 else 0) := by
    funext c
    rfl
  rw [hWord1, hWord2]
  rw [HammingWeight_sum_elim_eq]
  have hZero : HammingWeight
      (fun _ : xZero × classicalBit ↦ (0 : ZMod 2)) = 0 := by
    rw [HammingWeight_eq_zero_iff]
    rfl
  rw [hZero, zero_add]
  have hRight := HammingWeight_fixed_base_coordinate_eq
    x2 (fun a ↦ D.classicalBoundary b a)
  have hLeft' : HammingWeight
      (fun p : xOne × classicalCheck ↦
        if p.2 = b then D.xBoundary2 p.1 x2 else 0) =
      HammingWeight (fun x1 ↦ D.xBoundary2 x1 x2) := by
    exact HammingWeight_reverse_fiber_coordinate_eq (fun x1 ↦ D.xBoundary2 x1 x2) b
  rw [hLeft', hRight]
end QEC.Coding.DistanceBalancing
