-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.representationFamilyMarkovLinear_pair_of_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/4cca0fb4-1082-43ab-9298-613415b9c002

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
    {G ι H : Type*} [Group G] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : SoficGroups.UnitaryRepresentation G H)
    (s : ι → G) (v : G × G → H)
    (hequivariant : ∀ a g h : G,
      π a (v (g, h)) = v (a * g, a * h))
    (q : G × G) :
    representationFamilyMarkovLinear π s (v q) =
      pairedWordAverage s v 1 q := by
  rcases q with ⟨g, h⟩
  simp [representationFamilyMarkovLinear, pairedWordAverage,
    hequivariant]
end SoficGroups.KunRootedWordPower
