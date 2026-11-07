-- Prove2me | solution 1 for QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.logicalZPhysical_implements
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:18:21.358007+00:00
-- url     : https://prove2.me/submissions/e60d5b1a-39ae-463b-bed9-3eeb5b42a0e4

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Phase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_WeightedTriorthogonalCSS
import Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_logicalZPhysical_intertwines_basis

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Why24WeightedTriorthogonalCSS
open QEC.Coding QEC.Semantics
open scoped BigOperators
open QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
variable {Logical Stabilizer Site : Type}
variable [Fintype Logical] [DecidableEq Logical]
variable [Fintype Stabilizer] [DecidableEq Stabilizer]
variable [Fintype Site] [DecidableEq Site]
namespace QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
theorem _root_.solution
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a : Logical) (gamma : F1024) :
    R.encodedCode.ImplementsLogicalGate
      (R.logicalZPhysical a gamma) (R.logicalZLogical a gamma) := by
  intro psi
  let encodeAmbient :
      ComputationalBasisRegister F1024 Logical →ₗ[Complex]
        ComputationalBasisRegister F1024 Site :=
    R.encodedCode.code.carrier.subtype.comp R.encodedCode.encoding.toLinearMap
  have hlinear :
      (R.logicalZPhysical a gamma).toLinearEquiv.toLinearMap.comp encodeAmbient =
        encodeAmbient.comp (R.logicalZLogical a gamma).toLinearEquiv.toLinearMap := by
    apply (EuclideanSpace.basisFun (Logical → F1024) Complex).toBasis.ext
    intro u
    change R.logicalZPhysical a gamma
        (R.encodedCode.encode (registerBasisKet u)) =
      R.encodedCode.encode (R.logicalZLogical a gamma (registerBasisKet u))
    exact R.logicalZPhysical_intertwines_basis a gamma u
  exact LinearMap.congr_fun hlinear psi
end QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
