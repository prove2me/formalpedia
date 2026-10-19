-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.diagonalPairKernelUnitaryRepresentation_kerFun_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/81fd0bc4-2955-4e20-88c8-6c44ba5c9ba0

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_actionKernelUnitaryRepresentation_kerFun_one

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {G : Type u} [Group G]
    (K : Matrix (G × G) (G × G) ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (hinv : ∀ a g h j k : G,
      K (a * g, a * h) (a * j, a * k) = K (g, h) (j, k))
    (a g h : G) :
    diagonalPairKernelUnitaryRepresentation K hinv a
      (RKHS.kerFun (RKHS.OfKernel (scalarOperatorKernel K))
        (g, h) (1 : ℂ)) =
      RKHS.kerFun (RKHS.OfKernel (scalarOperatorKernel K))
        (a * g, a * h) (1 : ℂ) := by
  exact actionKernelUnitaryRepresentation_kerFun_one K
    (diagonalPairAction G)
    (fun a x y => hinv a x.1 x.2 y.1 y.2) a (g, h)
end SoficGroups.KunRootedIndicatorCrossing
