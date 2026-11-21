-- Prove2me | solution 1 for RungeKuttaOrderConditions.Butcher.gauss_order4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:59:32.914348+00:00
-- url     : https://prove2.me/submissions/494ae091-0787-4bff-a37d-2c4f92080084

module
public import Mathlib.Algebra.Ring.Rat
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_RungeKuttaOrderConditions_ButcherOrder
public import Theorems.Thm_RungeKuttaOrderConditions_Butcher_satisfiesOrderConditions_iff
section
@[expose] public section
namespace RungeKuttaOrderConditions
namespace Q15
end Q15
namespace Z15
end Z15
namespace Butcher
end Butcher
end RungeKuttaOrderConditions
namespace RungeKuttaOrderConditions.Butcher
end Butcher
end RungeKuttaOrderConditions
namespace RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
end Butcher
end RungeKuttaOrderConditions
namespace RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
end Butcher
end RungeKuttaOrderConditions
namespace RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
private theorem catalogFourEq : catalog 4 = treesUpToFour := rfl
private theorem gaussOnesReplicate :
    List.replicate gaussA.length (1 : Q15) = gaussOnes := by
  simp [gaussA, gaussOnes]
private theorem gaussCPmulOnes : pmul gaussC gaussOnes = gaussC := by
  simp [pmul, gaussC, gaussOnes]
private theorem gaussAcPmulOnes : pmul gaussAc gaussOnes = gaussAc := by
  simp [pmul, gaussAc, gaussOnes]
private theorem gaussAAcPmulOnes : pmul gaussAAc gaussOnes = gaussAAc := by
  simp [pmul, gaussAAc, gaussOnes]
private theorem gaussFirstStageVector : mulMatVec gaussA gaussOnes = gaussC := by
  simp only [mulMatVec, dot, gaussA, gaussOnes, gaussC, List.map_cons, List.map_nil,
    List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil,
    mul_one, add_zero, List.cons.injEq]
  constructor
  · ext <;> norm_num
  constructor
  · ext <;> norm_num
  constructor
  · ext <;> norm_num
  · trivial
private theorem gaussSecondStageVector : mulMatVec gaussA gaussC = gaussAc := by
  simp only [mulMatVec, dot, gaussA, gaussC, gaussAc, List.map_cons, List.map_nil,
    List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil,
    add_zero, List.cons.injEq]
  constructor
  · ext <;> norm_num
  constructor
  · ext <;> norm_num
  constructor
  · ext <;> norm_num
  · trivial
private theorem gaussThirdStageVector : mulMatVec gaussA gaussAc = gaussAAc := by
  simp only [mulMatVec, dot, gaussA, gaussAc, gaussAAc, List.map_cons, List.map_nil,
    List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil,
    add_zero, List.cons.injEq]
  constructor
  · ext <;> norm_num
  constructor
  · ext <;> norm_num
  constructor
  · ext <;> norm_num
  · trivial
private theorem gaussLeafVector : phiVec gaussA leaf = gaussOnes := by
  change List.replicate gaussA.length (1 : Q15) = gaussOnes
  exact gaussOnesReplicate
private theorem gaussT2Vector : phiVec gaussA t2 = gaussC := by
  change pmul (mulMatVec gaussA (phiVec gaussA leaf))
      (List.replicate gaussA.length (1 : Q15)) = gaussC
  rw [gaussLeafVector, gaussFirstStageVector, gaussOnesReplicate, gaussCPmulOnes]
private theorem gaussT32Vector : phiVec gaussA t32 = gaussAc := by
  change pmul (mulMatVec gaussA (phiVec gaussA t2))
      (List.replicate gaussA.length (1 : Q15)) = gaussAc
  rw [gaussT2Vector, gaussSecondStageVector, gaussOnesReplicate, gaussAcPmulOnes]
private theorem gaussT44Vector : phiVec gaussA t44 = gaussAAc := by
  change pmul (mulMatVec gaussA (phiVec gaussA t32))
      (List.replicate gaussA.length (1 : Q15)) = gaussAAc
  rw [gaussT32Vector, gaussThirdStageVector, gaussOnesReplicate, gaussAAcPmulOnes]
private theorem gaussT44Weight : Phi gaussA gaussB t44 = ⟨1 / 24, 0⟩ := by
  change dot gaussB (phiVec gaussA t44) = ⟨1 / 24, 0⟩
  rw [gaussT44Vector]
  simp only [dot, gaussB, gaussAAc, List.zipWith_cons_cons, List.zipWith_nil_right,
    List.sum_cons, List.sum_nil, add_zero]
  ext <;> norm_num
private theorem gaussCondition01 : orderCond gaussA gaussB t1 := by
  decide +kernel
private theorem gaussCondition02 : orderCond gaussA gaussB t2 := by
  decide +kernel
private theorem gaussCondition03 : orderCond gaussA gaussB t31 := by
  decide +kernel
private theorem gaussCondition04 : orderCond gaussA gaussB t41 := by
  decide +kernel
private theorem gaussCondition05 : orderCond gaussA gaussB t42 := by
  decide +kernel
private theorem gaussCondition06 : orderCond gaussA gaussB t32 := by
  decide +kernel
private theorem gaussCondition07 :
    orderCond gaussA gaussB (.node [.node [leaf], leaf]) := by
  decide +kernel
private theorem gaussCondition08 : orderCond gaussA gaussB t43 := by
  decide +kernel
private theorem gaussCondition09 : orderCond gaussA gaussB t44 := by
  change (gamma t44 : Q15) * Phi gaussA gaussB t44 = 1
  rw [gaussT44Weight]
  have hgamma : gamma t44 = 24 := by
    norm_num [gamma, gammaF, order, orderF, t44, leaf]
  rw [hgamma, Q15.natCast_eq]
  ext <;> norm_num
end Butcher
end RungeKuttaOrderConditions
end
end

set_option autoImplicit true
@[expose] public section
public section
open RungeKuttaOrderConditions RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
namespace RungeKuttaOrderConditions.Butcher
theorem _root_.solution : satisfiesOrderConditions gaussA gaussB 4 := by
  rw [satisfiesOrderConditions_iff, catalogFourEq]; intro t ht
  fin_cases ht
  · exact gaussCondition01
  · exact gaussCondition02
  · exact gaussCondition03
  · exact gaussCondition04
  · exact gaussCondition05
  · exact gaussCondition06
  · exact gaussCondition07
  · exact gaussCondition08
  · exact gaussCondition09
end RungeKuttaOrderConditions.Butcher
