-- Prove2me | solution 1 for QEC.Coding.DistanceBalancingSubsystem.kernelTensorToZLogicalSlices_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:38:31.491054+00:00
-- url     : https://prove2.me/submissions/561286b1-e597-4bad-b96e-b5132d82eeb0

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Definitions.Def_QEC_Coding_ChainComplex_Homotopy
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Subsystem

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancingSubsystem
open QEC.Coding
open QEC.Coding.DistanceBalancing
open scoped TensorProduct
universe u v
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Nonempty classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable {LogicalZ LogicalX : Type v}
variable [AddCommGroup LogicalZ] [Module (ZMod 2) LogicalZ]
variable [AddCommGroup LogicalX] [Module (ZMod 2) LogicalX]
variable [Module.Finite (ZMod 2) LogicalZ]
variable [Module.Finite (ZMod 2) LogicalX]
variable (SD : SubsystemCSSData xZero xOne xTwo LogicalZ LogicalX)
variable (Y : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
  Word (ZMod 2) classicalCheck)
namespace QEC.Coding.DistanceBalancingSubsystem
theorem _root_.solution :
    Function.Injective (kernelTensorToZLogicalSlices SD Y) := by
  apply Function.Injective.comp
    (TensorProduct.piScalarRight (ZMod 2) (ZMod 2)
      LogicalZ classicalBit).injective
  exact Module.Flat.lTensor_preserves_injective_linearMap
    (ClassicalKernel (productData SD Y)).subtype
    (ClassicalKernel (productData SD Y)).injective_subtype
end QEC.Coding.DistanceBalancingSubsystem
