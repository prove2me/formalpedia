-- Prove2me | solution 1 for QEC.Bounds.BPTEntropy.vonNeumannEntropy_abc_le_c_selectedDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:09:32.505626+00:00
-- url     : https://prove2.me/submissions/2aaf8132-9650-462d-976f-befe80f48424

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Theorems.Thm_QEC_Bounds_BPTEntropy_vonNeumannEntropy_abc_le_c_of_conditional_substitutions
import Theorems.Thm_QEC_Semantics_QuditSubsystem_vonNeumannEntropy_le_sum_log_selectedDimensions


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
open QEC.Bounds.BPTEntropy
open Semantics
open Semantics.DensityOperator
universe u
namespace QEC.Bounds.BPTEntropy
theorem _root_.solution
    (A B : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (regionC : QuditSubsystem q)
    (rho : DensityOperator (CompositeSystem A (CompositeSystem B regionC.selectedSystem)))
    (hA : rho.vonNeumannEntropy - (leftMarginal rho).vonNeumannEntropy =
      - (rightMarginal rho).vonNeumannEntropy)
    (hB : rho.vonNeumannEntropy -
        (leftMarginal ((abcToBac A B regionC.selectedSystem).conjDensity rho)).vonNeumannEntropy =
      - (rightMarginal ((abcToBac A B regionC.selectedSystem).conjDensity rho)).vonNeumannEntropy) :
    rho.vonNeumannEntropy <=
      ∑ i ∈ regionC.selected, Real.logb 2 (q i : Real) := by
  exact (vonNeumannEntropy_abc_le_c_of_conditional_substitutions A B regionC.selectedSystem
    rho hA hB).trans
      (regionC.vonNeumannEntropy_le_sum_log_selectedDimensions (leftMarginal (leftMarginal rho)))
end QEC.Bounds.BPTEntropy
