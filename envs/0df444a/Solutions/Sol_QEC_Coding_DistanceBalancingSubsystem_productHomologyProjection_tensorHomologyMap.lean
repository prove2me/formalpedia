-- Prove2me | solution 1 for QEC.Coding.DistanceBalancingSubsystem.productHomologyProjection_tensorHomologyMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:46:59.695198+00:00
-- url     : https://prove2.me/submissions/ab5e1dc8-0382-42c9-a768-6490ad40f40c

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Definitions.Def_QEC_Coding_ChainComplex_Homotopy
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Subsystem
import Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_kernelTensorZLogicalRetraction_apply
import Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_selectedHomologySliceMap_comp_tensorHomologyMap

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
theorem _root_.solution
    (t : (sourceChainComplex (productData SD Y)).middleHomology ⊗[ZMod 2]
      ClassicalKernel (productData SD Y)) :
    productHomologyProjection SD Y
        (tensorHomologyMap (productData SD Y) t) =
      sourceLogicalTensorProjection SD Y t := by
  rw [productHomologyProjection, LinearMap.comp_apply]
  have hSlices := LinearMap.congr_fun
    (selectedHomologySliceMap_comp_tensorHomologyMap SD Y) t
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hSlices
  rw [hSlices, kernelTensorZLogicalRetraction_apply]
end QEC.Coding.DistanceBalancingSubsystem
