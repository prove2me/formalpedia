-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.eventually_rooted_of_growing_word_radius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/a812c531-2fe9-4c22-bdce-046bbf1fc45d

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v w
namespace SoficGroups.KunRootedWordPower
theorem _root_.solution
    {G ι : Type u} [Group G]
    (X : ℕ → RootedIndicatorMarkovModel G ι)
    (w : G → List ι)
    (hroot : ∀ n, (X n).IsRootedAtRadius w n)
    (a g : G) :
    ∀ᶠ n in Filter.atTop,
      ∀ x : (X n).carrier,
        indicatorVector (X n).indicator x ≠ 0 →
          (X n).evaluation (a * g) x =
            ((X n).evaluation a * (X n).evaluation g) x := by
  filter_upwards [Filter.eventually_ge_atTop
    ((w a).length + (w g).length + (w (a * g)).length)]
      with n hn
  exact (hroot n).out a g hn
end SoficGroups.KunRootedWordPower
