-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.checkSupport_card_le_of_boundedLocality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:25:57.932959+00:00
-- url     : https://prove2.me/submissions/7bffe4b9-d133-4ba6-b44f-d66dd6118bb0

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
    (h : BoundedLocality I.localityProfile B) (c : check) :
    (I.checkSupport c).card ≤ B := by
  have hc : (I.checkSupport c).card ≤
      Finset.univ.sup (fun c' ↦ (I.checkSupport c').card) :=
    Finset.le_sup (f := fun c' ↦ (I.checkSupport c').card)
      (Finset.mem_univ c)
  exact hc.trans h.1
end QEC.Coding.DistanceBalancing
