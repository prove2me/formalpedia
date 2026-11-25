-- Prove2me | solution 1 for P2M_Darpa018_H2Core_hasSection_iff_isCoboundary__4ff7078dc15b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:32:03.904695+00:00
-- url     : https://prove2.me/submissions/1cd90ed4-b766-489c-a8f4-eb7a32ed3411

module
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Tactic.Abel
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Tactic.NoncommRing
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Tactic.Group
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Definitions.Def_DarpaH2Lifting_Solution

set_option autoImplicit false
@[expose] public section
public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Darpa018 Darpa018.H2Core
variable {G M : Type}
variable [Group G] [AddCommGroup M] [DistribMulAction G M]
namespace Darpa018.H2Core
theorem _root_.solution
    (c : G × G → M) :
    HasSection c ↔ groupCohomology.IsCoboundary₂ c := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun g => -t g, ?_⟩
    intro g h
    change g • (-t h) - (-t (g * h)) + (-t g) = c (g, h)
    rw [smul_neg]
    calc
      -(g • t h) - (-t (g * h)) + (-t g) =
          t (g * h) - (t g + g • t h) := by abel
      _ = c (g, h) := by rw [ht g h]; abel
  · rintro ⟨s, hs⟩
    refine ⟨fun g => -s g, ?_⟩
    intro g h
    change -s (g * h) = -s g + g • (-s h) + c (g, h)
    rw [smul_neg, ← hs g h]
    abel
end Darpa018.H2Core
