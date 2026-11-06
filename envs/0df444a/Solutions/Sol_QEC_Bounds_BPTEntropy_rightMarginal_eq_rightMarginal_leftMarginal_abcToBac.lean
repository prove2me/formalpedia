-- Prove2me | solution 1 for QEC.Bounds.BPTEntropy.rightMarginal_eq_rightMarginal_leftMarginal_abcToBac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:27:05.330581+00:00
-- url     : https://prove2.me/submissions/e67d50cf-514f-424a-8ea1-d7b2b5c3837d

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Theorems.Thm_QEC_Bounds_BPTEntropy_rightMarginal_leftMarginal_eq_rightMarginal_abcToBac
import Theorems.Thm_QEC_Bounds_BPTEntropy_abcToBac_reverse_conjDensity

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
    (rho : DensityOperator (CompositeSystem A (CompositeSystem B C))) :
    rightMarginal rho =
      rightMarginal (leftMarginal ((abcToBac A B C).conjDensity rho)) := by
  have hswap := rightMarginal_leftMarginal_eq_rightMarginal_abcToBac B A C
    ((abcToBac A B C).conjDensity rho)
  rw [abcToBac_reverse_conjDensity A B C rho] at hswap
  exact hswap.symm
end QEC.Bounds.BPTEntropy
