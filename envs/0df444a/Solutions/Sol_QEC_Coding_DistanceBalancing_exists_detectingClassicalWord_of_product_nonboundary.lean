-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.exists_detectingClassicalWord_of_product_nonboundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:55:51.849234+00:00
-- url     : https://prove2.me/submissions/c7808c53-614e-49f7-a8af-15ea4f987ad3

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_classicalWordOfHomologyFunctional_mem_kernel
import Theorems.Thm_QEC_Coding_DistanceBalancing_mul_HammingWeight_classicalWordOfHomologyFunctional_le
import Theorems.Thm_QEC_Coding_DistanceBalancing_exists_sourceHomologySlice_ne_zero_of_product_nonboundary
import Theorems.Thm_QEC_Coding_DistanceBalancing_exists_homologyFunctional_eq_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open scoped BigOperators
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)
namespace QEC.Coding.DistanceBalancing
theorem _root_.solution
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    {dSource : Nat}
    (hSource : MiddleHomologyDistanceAtLeast
      (sourceChainComplex D) dSource)
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (hNonboundary : z ∉ (chainComplex D).middleBoundaryCode.carrier) :
    ∃ w : Word (ZMod 2) classicalBit,
      Matrix.toLin' D.classicalBoundary w = 0 ∧
      w ≠ 0 ∧
      dSource * HammingWeight w ≤ HammingWeight z := by
  obtain ⟨a, hClass⟩ :=
    exists_sourceHomologySlice_ne_zero_of_product_nonboundary
      D S hS z hz hNonboundary
  obtain ⟨φ, hφ⟩ := exists_homologyFunctional_eq_one D hClass
  let w := classicalWordOfHomologyFunctional D z hz φ
  refine ⟨w, classicalWordOfHomologyFunctional_mem_kernel D z hz φ,
    ?_, mul_HammingWeight_classicalWordOfHomologyFunctional_le
      D hSource z hz φ⟩
  intro hw
  have hAt := congrFun hw a
  change φ (sourceHomologySlice D z hz a) = 0 at hAt
  rw [hφ] at hAt
  exact one_ne_zero hAt
end QEC.Coding.DistanceBalancing
