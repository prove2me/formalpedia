-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.HammingWeight_transpose_boundary1_single_inl_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:43:04.20765+00:00
-- url     : https://prove2.me/submissions/6e267b31-172d-494f-be86-c871010a57cf

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
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
    (x0 : xZero) (a : classicalBit) :
    HammingWeight
        (wordLinearMapTranspose (boundary1 D)
          (Pi.single (Sum.inl (x0, a)) 1)) =
      HammingWeight (fun x1 ↦ D.xBoundary1 x0 x1) := by
  rw [boundary1, wordLinearMapTranspose_matrixToLin_single]
  have hWord : (fun c ↦ boundary1Matrix D (Sum.inl (x0, a)) c) =
      (Sum.elim
        (fun p : xOne × classicalBit ↦
          if a = p.2 then D.xBoundary1 x0 p.1 else 0)
        (fun _ : xTwo × classicalCheck ↦ 0)) := by
    funext c
    cases c <;> rfl
  rw [hWord]
  rw [HammingWeight_sum_elim_eq]
  have hZero : HammingWeight
      (fun _ : xTwo × classicalCheck ↦ (0 : ZMod 2)) = 0 := by
    rw [HammingWeight_eq_zero_iff]
    rfl
  rw [hZero, Nat.add_zero]
  exact HammingWeight_one_fiber_coordinate_eq
      (fun x1 ↦ D.xBoundary1 x0 x1)
      (fun _ ↦ Equiv.refl classicalBit) a
end QEC.Coding.DistanceBalancing
