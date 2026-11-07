-- Prove2me | solution 1 for QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.logicalXPhysical_implements
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:18:04.897765+00:00
-- url     : https://prove2.me/submissions/ca457836-0dbb-49a8-9fc3-59de23ab005b

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Phase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_WeightedTriorthogonalCSS
import Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_logicalXPhysical_intertwines_basis

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
    (a : Logical) (beta : F1024) :
    R.encodedCode.ImplementsLogicalGate
      (R.logicalXPhysical a beta) (R.logicalXLogical a beta) := by
  intro psi
  let encodeAmbient :
      ComputationalBasisRegister F1024 Logical →ₗ[Complex]
        ComputationalBasisRegister F1024 Site :=
    R.encodedCode.code.carrier.subtype.comp R.encodedCode.encoding.toLinearMap
  have hlinear :
      (R.logicalXPhysical a beta).toLinearEquiv.toLinearMap.comp encodeAmbient =
        encodeAmbient.comp (R.logicalXLogical a beta).toLinearEquiv.toLinearMap := by
    apply (EuclideanSpace.basisFun (Logical → F1024) Complex).toBasis.ext
    intro u
    change R.logicalXPhysical a beta
        (R.encodedCode.encode (registerBasisKet u)) =
      R.encodedCode.encode (R.logicalXLogical a beta (registerBasisKet u))
    exact R.logicalXPhysical_intertwines_basis a beta u
  exact LinearMap.congr_fun hlinear psi
end QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
