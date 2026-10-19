-- Prove2me | solution 1 for SoficGroups.KunFinitePermutationMarkovMass.sum_realIndicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/4aac1870-23a9-48de-8d7b-c67c68c3298b

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunFinitePermutationMarkovMass
open scoped BigOperators
namespace SoficGroups.KunFinitePermutationMarkovMass
theorem _root_.solution {V : Type*}
    [Fintype V] [DecidableEq V] (T : Finset V) :
    (∑ x : V, realIndicator T x) = (T.card : ℝ) := by
  classical
  simp [realIndicator]
end SoficGroups.KunFinitePermutationMarkovMass
