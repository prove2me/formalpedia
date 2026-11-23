-- Prove2me | solution 1 for ReciprocityTheory.Coh.ContinuousSections.rep_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:52.133205+00:00
-- url     : https://prove2.me/submissions/4a407d97-7910-4a04-977c-1189e286dd8b

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Definitions.Def_ReciprocityTheory_GroupCohomology_SectionA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Pointwise Set
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.ContinuousSections
variable {G : Type*} [Group G]
namespace ReciprocityTheory.Coh.ContinuousSections
theorem _root_.solution (K N : Subgroup G) [N.Normal] {x y : G} (h : (rel K N) x y) : rep K N x = rep K N y := by
  unfold rep
  rw [Quotient.sound (s := rel K N) h]
end ReciprocityTheory.Coh.ContinuousSections
