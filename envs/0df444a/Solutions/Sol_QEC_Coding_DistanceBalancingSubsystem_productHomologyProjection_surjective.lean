-- Prove2me | solution 1 for QEC.Coding.DistanceBalancingSubsystem.productHomologyProjection_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:48:58.339339+00:00
-- url     : https://prove2.me/submissions/05bb6ef4-32a8-4f14-a129-58fa7125cc83

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Definitions.Def_QEC_Coding_ChainComplex_Homotopy
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Subsystem
import Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_sourceHomologyProjection_surjective
import Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_productHomologyProjection_tensorHomologyMap

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
    Function.Surjective (productHomologyProjection SD Y) := by
  intro z
  have hTensor : Function.Surjective (sourceLogicalTensorProjection SD Y) := by
    apply TensorProduct.map_surjective
    · exact sourceHomologyProjection_surjective SD Y
    · intro w
      exact ⟨w, rfl⟩
  obtain ⟨t, rfl⟩ := hTensor z
  exact ⟨tensorHomologyMap (productData SD Y) t,
    productHomologyProjection_tensorHomologyMap SD Y t⟩
end QEC.Coding.DistanceBalancingSubsystem
