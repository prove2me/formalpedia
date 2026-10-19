-- Prove2me | solution 1 for SoficGroups.KunGuardedCanonicalMatchedDensity.matchedRadiusBad_mono_bad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/7044db6a-4cbf-44a5-b5ad-2570f4220b50

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunGuardedCanonicalMatchedDensity
open Filter Topology
namespace SoficGroups.KunGuardedCanonicalMatchedDensity
theorem _root_.solution
    {V ι : Type*} [DecidableEq V]
    {U : Finset V} (P : Finpartition U)
    (I : Finset ι) (w : ι → Equiv.Perm V)
    {B B' : Finset V} (hB : B ⊆ B') :
    SoficGroups.matchedRadiusBad P I w B ⊆
      SoficGroups.matchedRadiusBad P I w B' := by
  intro x hx
  unfold SoficGroups.matchedRadiusBad at hx ⊢
  rcases Finset.mem_union.mp hx with hxB | hxcross
  · exact Finset.mem_union_left _ (hB hxB)
  · exact Finset.mem_union_right _ hxcross
end SoficGroups.KunGuardedCanonicalMatchedDensity
