-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.variableSupport_card_le_of_boundedLocality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:25:59.457193+00:00
-- url     : https://prove2.me/submissions/5984139a-c7ed-4bc3-9452-9383ade631e0

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open QEC.Coding.FiberBundle
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)
namespace QEC.Coding.DistanceBalancing
theorem _root_.solution
    {check var : Type u} [Fintype check] [Fintype var]
    (I : QEC.QLDPC.CheckIncidence check var) {B : Nat}
    (h : BoundedLocality I.localityProfile B) (q : var) :
    (I.variableSupport q).card ≤ B := by
  have hq : (I.variableSupport q).card ≤
      Finset.univ.sup (fun q' ↦ (I.variableSupport q').card) :=
    Finset.le_sup (f := fun q' ↦ (I.variableSupport q').card)
      (Finset.mem_univ q)
  exact hq.trans h.2
end QEC.Coding.DistanceBalancing
