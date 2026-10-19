-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.norm_normalizedIndicatorDefect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/be08c839-92f7-4a27-bb14-8923200106a5

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
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (hdefect : permutationMarkov p (indicatorVector f) ≠
      indicatorVector f) :
    ‖normalizedIndicatorDefect p f‖ = 1 := by
  have hne : ‖permutationMarkov p (indicatorVector f) -
      indicatorVector f‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr hdefect)
  simp [normalizedIndicatorDefect, norm_smul, norm_inv,
    Complex.norm_real, hne]
end SoficGroups.KunRootedIndicatorCrossing
