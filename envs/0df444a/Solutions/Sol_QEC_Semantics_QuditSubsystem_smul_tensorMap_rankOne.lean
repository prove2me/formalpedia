-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.smul_tensorMap_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:54:47.908562+00:00
-- url     : https://prove2.me/submissions/6d0ed95e-6949-47e1-a0f3-f1676b6a7ceb

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (c : Complex) (x y : H) (u v : K) :
    c • (InnerProductSpace.rankOne Complex (x ⊗ₜ[Complex] u)
      (y ⊗ₜ[Complex] v)).toLinearMap =
      TensorProduct.map (c • (InnerProductSpace.rankOne Complex x y).toLinearMap)
        (InnerProductSpace.rankOne Complex u v).toLinearMap := by
  rw [TensorProduct.map_smul_left, tensorMap_rankOne]
end QEC.Semantics.QuditSubsystem
