-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.ofKernel_kerFun_one_eq_coe_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/1b5d954b-a8b0-4e10-8666-250a02bc477b

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {I : Type u} (L : Matrix I I (ℂ →L[ℂ] ℂ))
    [Fact L.PosSemidef] (i : I) :
    RKHS.kerFun (RKHS.OfKernel L) i (1 : ℂ) =
      ((Finsupp.single (i, (1 : ℂ)) (1 : ℂ) : RKHS.H₀ L) :
        RKHS.OfKernel L) := by
  simp [RKHS.kerFun, RKHS.coeCLM]
end SoficGroups.KunRootedIndicatorCrossing
