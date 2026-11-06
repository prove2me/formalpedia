-- Prove2me | solution 1 for QEC.Bounds.BPTEntropy.vonNeumannEntropy_abc_le_c_of_conditional_substitutions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:33:50.257205+00:00
-- url     : https://prove2.me/submissions/e705d7cc-08a6-48e2-9456-be1d6e6c901e

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Theorems.Thm_QEC_Bounds_BPTEntropy_rightMarginal_leftMarginal_eq_rightMarginal_abcToBac
import Theorems.Thm_QEC_Bounds_BPTEntropy_rightMarginal_eq_rightMarginal_leftMarginal_abcToBac
import Theorems.Thm_QEC_Bounds_BPTEntropy_leftMarginal_leftMarginal_eq_leftMarginal_leftMarginal_abcToBac
import Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_subadditive_bipartite


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
    (A B C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C]
    (rho : DensityOperator (CompositeSystem A (CompositeSystem B C)))
    (hA : rho.vonNeumannEntropy - (leftMarginal rho).vonNeumannEntropy =
      - (rightMarginal rho).vonNeumannEntropy)
    (hB : rho.vonNeumannEntropy -
        (leftMarginal ((abcToBac A B C).conjDensity rho)).vonNeumannEntropy =
      - (rightMarginal ((abcToBac A B C).conjDensity rho)).vonNeumannEntropy) :
    rho.vonNeumannEntropy <= (leftMarginal (leftMarginal rho)).vonNeumannEntropy := by
  have hsubBC := vonNeumannEntropy_subadditive_bipartite (leftMarginal rho)
  have hsubAC := vonNeumannEntropy_subadditive_bipartite
    (leftMarginal ((abcToBac A B C).conjDensity rho))
  rw [rightMarginal_leftMarginal_eq_rightMarginal_abcToBac A B C rho] at hsubBC
  rw [← rightMarginal_eq_rightMarginal_leftMarginal_abcToBac A B C rho] at hsubAC
  rw [← leftMarginal_leftMarginal_eq_leftMarginal_leftMarginal_abcToBac A B C rho] at hsubAC
  linarith
end QEC.Bounds.BPTEntropy
