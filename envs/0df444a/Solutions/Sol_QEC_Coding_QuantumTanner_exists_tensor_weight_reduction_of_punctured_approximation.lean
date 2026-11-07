-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.exists_tensor_weight_reduction_of_punctured_approximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:17:00.527836+00:00
-- url     : https://prove2.me/submissions/79f1a896-5595-4487-8f0b-eaea4b10a51d

import Definitions.Def_QEC_Coding_QuantumTanner_TensorApproximation
import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture
import Definitions.Def_QEC_Coding_QuantumTanner_Distance
import Definitions.Def_QEC_Coding_QuantumTanner_LocalReduction
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_tensorCode_lift_punctured
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_tensor_approximation_of_robust
import Theorems.Thm_QEC_Coding_QuantumTanner_hammingWeight_tensorPuncture_loss_le


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
variable {A B : Type v} [Fintype A] [Fintype B]
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (removedA : Finset A) (removedB : Finset B)
    (dA dB w : Nat)
    (hA : MinimumDistance (puncturedCode CA removedA) dA)
    (hB : MinimumDistance (puncturedCode CB removedB) dB)
    (hRobust : IsRobust (puncturedCode CA removedA) (puncturedCode CB removedB) w)
    (hBudget : 2 * w ≤ dA * dB)
    (x : Word (ZMod 2) (A × B))
    (C R : Word (ZMod 2) (KeptCoordinate removedA × KeptCoordinate removedB))
    (hC : C ∈ (columnCode (puncturedCode CA removedA)).carrier)
    (hR : R ∈ (rowCode (puncturedCode CB removedB)).carrier)
    (hClose : HammingWeight (tensorPunctureMap removedA removedB x + C) +
      HammingWeight (tensorPunctureMap removedA removedB x + R) ≤ w)
    (hMargin : 3 * (HammingWeight (tensorPunctureMap removedA removedB x + C) +
      HammingWeight (tensorPunctureMap removedA removedB x + R)) +
        2 * (removedA.card * Fintype.card B + Fintype.card A * removedB.card) <
      2 * HammingWeight x) :
    ∃ c : Word (ZMod 2) (A × B), c ∈ (tensorCode CA CB).carrier ∧
      HammingWeight (x + c) < HammingWeight x := by
  obtain ⟨cKept, hcKept, hApprox⟩ := exists_tensor_approximation_of_robust
    (puncturedCode CA removedA) (puncturedCode CB removedB)
    dA dB w hA hB hRobust hBudget (tensorPunctureMap removedA removedB x)
    C R hC hR hClose
  obtain ⟨c, hc, hLift⟩ := exists_tensorCode_lift_punctured
    CA CB removedA removedB cKept hcKept
  have hLoss := hammingWeight_tensorPuncture_loss_le removedA removedB (x + c)
  rw [map_add, hLift] at hLoss
  exact ⟨c, hc, by omega⟩
end QEC.Coding.QuantumTanner
