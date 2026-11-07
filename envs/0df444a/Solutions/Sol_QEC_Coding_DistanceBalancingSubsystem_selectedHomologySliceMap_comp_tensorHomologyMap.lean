-- Prove2me | solution 1 for QEC.Coding.DistanceBalancingSubsystem.selectedHomologySliceMap_comp_tensorHomologyMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:41:24.462211+00:00
-- url     : https://prove2.me/submissions/dfe02f4f-d5ca-466e-b43a-4fda1d90b0ba

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Definitions.Def_QEC_Coding_ChainComplex_Homotopy
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Subsystem
import Theorems.Thm_QEC_Coding_DistanceBalancing_homologySliceMap_tensorHomologyMap_tmul


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
    (selectedHomologySliceMap SD Y).comp
        (tensorHomologyMap (productData SD Y)) =
      (kernelTensorToZLogicalSlices SD Y).comp
        (sourceLogicalTensorProjection SD Y) := by
  apply TensorProduct.ext'
  intro h w
  ext a
  change sourceHomologyProjection SD Y
      (homologySliceMap (productData SD Y)
        (tensorHomologyMap (productData SD Y) (h ⊗ₜ[ZMod 2] w)) a) =
    kernelTensorToZLogicalSlices SD Y
      (TensorProduct.map (sourceHomologyProjection SD Y) LinearMap.id
        (h ⊗ₜ[ZMod 2] w)) a
  rw [TensorProduct.map_tmul, kernelTensorToZLogicalSlices_tmul]
  rw [homologySliceMap_tensorHomologyMap_tmul, map_smul]
  rfl
end QEC.Coding.DistanceBalancingSubsystem
