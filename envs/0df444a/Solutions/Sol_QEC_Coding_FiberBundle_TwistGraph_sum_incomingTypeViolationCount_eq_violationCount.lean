-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.sum_incomingTypeViolationCount_eq_violationCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:05:22.700807+00:00
-- url     : https://prove2.me/submissions/d686ab0b-4485-4f9f-944e-27f8f545b237

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_sum_outgoingTypeViolationCount_eq_violationCount
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_incomingTypeViolationCount_eq_outgoing_inNeighbor

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    (∑ u : ZMod ell, ∑ τ : Fin typeCount,
      incomingTypeViolationCount baseSample twistSample w u τ) =
        violationCount baseSample twistSample w := by
  calc
    _ = ∑ τ : Fin typeCount, ∑ u : ZMod ell,
        incomingTypeViolationCount baseSample twistSample w u τ := by
          rw [Finset.sum_comm]
    _ = ∑ τ : Fin typeCount, ∑ u : ZMod ell,
        outgoingTypeViolationCount baseSample twistSample w
          (inNeighbor twistSample τ u) τ := by
          simp_rw [incomingTypeViolationCount_eq_outgoing_inNeighbor]
    _ = ∑ τ : Fin typeCount, ∑ u : ZMod ell,
        outgoingTypeViolationCount baseSample twistSample w u τ := by
          apply Fintype.sum_congr
          intro τ
          exact (typeTranslation twistSample τ).symm.sum_comp
            (fun u =>
              outgoingTypeViolationCount baseSample twistSample w u τ)
    _ = ∑ u : ZMod ell, ∑ τ : Fin typeCount,
        outgoingTypeViolationCount baseSample twistSample w u τ := by
          rw [Finset.sum_comm]
    _ = violationCount baseSample twistSample w :=
      sum_outgoingTypeViolationCount_eq_violationCount
        baseSample twistSample w
end QEC.Coding.FiberBundle.TwistGraph
