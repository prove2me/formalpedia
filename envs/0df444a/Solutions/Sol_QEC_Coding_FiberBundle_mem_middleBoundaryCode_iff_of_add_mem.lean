-- Prove2me | solution 1 for QEC.Coding.FiberBundle.mem_middleBoundaryCode_iff_of_add_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:10:59.205776+00:00
-- url     : https://prove2.me/submissions/05047221-187f-401e-b639-34f2a874e2ab

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z' z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hHomologous :
      z' + z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier) :
    z' ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ↔
      z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier := by
  let S := (chainComplex
    (RandomTwist.fiberBundleData baseSample twistSample)
    ).middleBoundaryCode.carrier
  have hCancelLeft : (z' + z) + z' = z := by
    funext q
    have hself : z' q + z' q = 0 := by
      calc
        z' q + z' q = z' q + (-z' q) := by
          rw [ZMod.neg_eq_self_mod_two]
        _ = 0 := add_neg_cancel _
    change (z' q + z q) + z' q = z q
    calc
      (z' q + z q) + z' q = (z' q + z' q) + z q := by abel
      _ = z q := by rw [hself, zero_add]
  have hCancelRight : (z' + z) + z = z' := by
    funext q
    have hself : z q + z q = 0 := by
      calc
        z q + z q = z q + (-z q) := by
          rw [ZMod.neg_eq_self_mod_two]
        _ = 0 := add_neg_cancel _
    change (z' q + z q) + z q = z' q
    calc
      (z' q + z q) + z q = z' q + (z q + z q) := by abel
      _ = z' q := by rw [hself, add_zero]
  constructor
  · intro hz'
    have hsum : (z' + z) + z' ∈ S :=
      Submodule.add_mem S hHomologous hz'
    rw [hCancelLeft] at hsum
    exact hsum
  · intro hz
    have hsum : (z' + z) + z ∈ S :=
      Submodule.add_mem S hHomologous hz
    rw [hCancelRight] at hsum
    exact hsum
end QEC.Coding.FiberBundle
