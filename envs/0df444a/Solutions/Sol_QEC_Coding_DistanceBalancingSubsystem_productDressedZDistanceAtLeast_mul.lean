-- Prove2me | solution 1 for QEC.Coding.DistanceBalancingSubsystem.productDressedZDistanceAtLeast_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:42:09.544577+00:00
-- url     : https://prove2.me/submissions/85bfa39b-0481-4d68-a6f0-4710f59655e0

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Definitions.Def_QEC_Coding_ChainComplex_Homotopy
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Subsystem
import Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_exists_ne_zero_coordinate
import Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_mul_hammingWeight_selectedFunctional_le
import Theorems.Thm_QEC_Coding_DistanceBalancing_classicalWordOfHomologyFunctional_mem_kernel
import Theorems.Thm_QEC_Coding_DistanceBalancing_distance_product_le_of_detectingClassicalWord


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
    {dSource dClassical : Nat}
    (hSource : SD.DressedZDistanceAtLeast dSource)
    (hClassical : ClassicalDistanceAtLeast
      (productData SD Y).classicalBoundary dClassical) :
    ProductDressedZDistanceAtLeast SD Y (dClassical * dSource) := by
  intro z hz hSelected
  obtain ⟨a, ha⟩ := exists_ne_zero_coordinate
    (selectedHomologySlices SD Y z hz) hSelected
  obtain ⟨phi, hphi⟩ :=
    Module.Projective.exists_dual_eq_one (ZMod 2) ha
  let psi : Module.Dual (ZMod 2)
      (sourceChainComplex (productData SD Y)).middleHomology :=
    phi.comp (sourceHomologyProjection SD Y)
  let w := classicalWordOfHomologyFunctional (productData SD Y) z hz psi
  have hwKernel : Matrix.toLin' (productData SD Y).classicalBoundary w = 0 :=
    classicalWordOfHomologyFunctional_mem_kernel
      (productData SD Y) z hz psi
  have hwNonzero : w ≠ 0 := by
    intro hw
    have hAt := congrFun hw a
    change phi (selectedHomologySlices SD Y z hz a) = 0 at hAt
    rw [hphi] at hAt
    exact one_ne_zero hAt
  have hwBound : dSource * HammingWeight w ≤ HammingWeight z := by
    exact mul_hammingWeight_selectedFunctional_le SD Y hSource z hz phi
  exact distance_product_le_of_detectingClassicalWord
    (productData SD Y) hClassical w hwKernel hwNonzero hwBound
end QEC.Coding.DistanceBalancingSubsystem
