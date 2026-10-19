-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.exists_equivariantHilbertKernelRealization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/cf88497e-407a-40ac-8a01-2add5fd40a2e

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_scalarOperatorKernel_posSemidef
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_diagonalPairKernelUnitaryRepresentation_kerFun_one

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
    (hpositive : K.PosSemidef)
    (hdiagonal : ∀ a g h j k : G,
      K (a * g, a * h) (a * j, a * k) = K (g, h) (j, k)) :
    Nonempty (EquivariantHilbertKernelRealization K) := by
  letI : Fact (scalarOperatorKernel K).PosSemidef :=
    ⟨scalarOperatorKernel_posSemidef K hpositive⟩
  let H := RKHS.OfKernel (scalarOperatorKernel K)
  let R : HilbertKernelRealization K := {
    carrier := H
    vector := fun q => RKHS.kerFun H q (1 : ℂ)
    gram := by
      intro q r
      rw [RKHS.kerFun_inner, RKHS.kerFun_apply,
        RKHS.OfKernel.kernel_ofKernel]
      simp [scalarOperatorKernel,
        ContinuousLinearMap.toSpanSingleton_apply]
  }
  refine ⟨{
    realization := R
    representation := diagonalPairKernelUnitaryRepresentation K hdiagonal
    equivariant := ?_
  }⟩
  intro a g h
  exact diagonalPairKernelUnitaryRepresentation_kerFun_one
    K hdiagonal a g h
end SoficGroups.KunRootedIndicatorCrossing
