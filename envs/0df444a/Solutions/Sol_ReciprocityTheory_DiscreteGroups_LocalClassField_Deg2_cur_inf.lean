-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.cur_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:52.48931+00:00
-- url     : https://prove2.me/submissions/f5918f8d-19a2-47e7-8908-83f9334fae76

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_CurriedCoboundaryEq
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HomFInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M)
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
theorem _root_.solution (hP : IsInvRep M N Q P) (z : Q.coch.X 2) (g h : G) :
    cur M (P.hom.f 2 z) g h = P.u (cur Q z (g : G ⧸ N) (h : G ⧸ N)) := by
  have hφa : ∀ a, P.φ a = (a : G ⧸ N) := fun a => by rw [hP.1]; rfl
  show P.u (z.1 _) = P.u (z.1 _)
  refine congrArg (fun v => P.u (z.1 v)) (funext fun i => ?_)
  fin_cases i
  · exact hφa g
  · exact hφa h
end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
