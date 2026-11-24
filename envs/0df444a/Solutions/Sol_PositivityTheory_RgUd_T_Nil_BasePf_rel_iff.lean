-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.BasePf.rel_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:07.704798+00:00
-- url     : https://prove2.me/submissions/665a7264-d082-4261-baec-ddef1876f2d9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_BaseOrbits_PieceMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set GroundTheory.Automorphic.Whittaker
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.BasePf
variable {Y W G : Type*} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace W] [T2Space W]
  [Group G] [MulAction G W]
namespace PositivityTheory.RgUd.T.Nil.BasePf
theorem _root_.solution (K : Subgroup G) (a b : W) :
    Quotient.mk (rel K) a = Quotient.mk (rel K) b ↔ ∃ g ∈ K, g • b = a :=
  Quotient.eq (r := rel K)
end PositivityTheory.RgUd.T.Nil.BasePf
