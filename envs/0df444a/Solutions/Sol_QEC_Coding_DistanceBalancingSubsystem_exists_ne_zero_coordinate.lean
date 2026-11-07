-- Prove2me | solution 1 for QEC.Coding.DistanceBalancingSubsystem.exists_ne_zero_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:33:16.488196+00:00
-- url     : https://prove2.me/submissions/7d5c0e14-f93e-4a53-9e0e-0bf50677262d

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
theorem _root_.solution
    {i M : Type*} [Nonempty i] [Zero M]
    (f : i → M) (hf : f ≠ 0) : ∃ i, f i ≠ 0 := by
  by_contra h
  apply hf
  funext i
  exact not_ne_iff.mp ((not_exists.mp h) i)
end QEC.Coding.DistanceBalancingSubsystem
