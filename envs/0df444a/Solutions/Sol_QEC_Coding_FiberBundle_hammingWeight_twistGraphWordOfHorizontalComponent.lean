-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_twistGraphWordOfHorizontalComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:11:24.818816+00:00
-- url     : https://prove2.me/submissions/ec8caa6b-6979-464a-8899-a116d5c20e3d

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_twistGraph_variableWord_eq_horizontalFiber
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_hammingWeight_eq_sum_variableWord
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_horizontalComponent_eq_sum_fibers


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r ell : Nat}
    [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hNormalized : IsHorizontallyResidueNormalized z) :
    HammingWeight (twistGraphWordOfHorizontalComponent z) =
      HammingWeight (horizontalComponent z) := by
  rw [TwistGraph.hammingWeight_eq_sum_variableWord,
    hammingWeight_horizontalComponent_eq_sum_fibers]
  apply Finset.sum_congr rfl
  intro b _hb
  exact hammingWeight_twistGraph_variableWord_eq_horizontalFiber
    z hNormalized b
end QEC.Coding.FiberBundle
