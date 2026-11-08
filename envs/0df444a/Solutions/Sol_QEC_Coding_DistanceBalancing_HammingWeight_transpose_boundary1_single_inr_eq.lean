-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.HammingWeight_transpose_boundary1_single_inr_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:47:23.569627+00:00
-- url     : https://prove2.me/submissions/3db3bdad-d38d-4b81-81cf-c83702e44ef4

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_fixed_base_coordinate_eq
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_one_fiber_coordinate_eq
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_sum_elim_eq
import Theorems.Thm_QEC_Coding_FiberBundle_wordLinearMapTranspose_matrixToLin_single


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
    (x1 : xOne) (b : classicalCheck) :
    HammingWeight
        (wordLinearMapTranspose (boundary1 D)
          (Pi.single (Sum.inr (x1, b)) 1)) =
      HammingWeight (fun a ↦ D.classicalBoundary b a) +
        HammingWeight (fun x2 ↦ D.xBoundary2 x1 x2) := by
  rw [boundary1, wordLinearMapTranspose_matrixToLin_single]
  have hWord : (fun c ↦ boundary1Matrix D (Sum.inr (x1, b)) c) =
      (Sum.elim
        (fun p : xOne × classicalBit ↦
          if x1 = p.1 then D.classicalBoundary b p.2 else 0)
        (fun p : xTwo × classicalCheck ↦
          if b = p.2 then D.xBoundary2 x1 p.1 else 0)) := by
    funext c
    cases c <;> rfl
  rw [hWord]
  rw [HammingWeight_sum_elim_eq]
  rw [HammingWeight_fixed_base_coordinate_eq]
  exact congrArg
    (fun n ↦ HammingWeight (fun a ↦ D.classicalBoundary b a) + n)
    (HammingWeight_one_fiber_coordinate_eq
      (fun x2 ↦ D.xBoundary2 x1 x2)
      (fun _ ↦ Equiv.refl classicalCheck) b)
end QEC.Coding.DistanceBalancing
