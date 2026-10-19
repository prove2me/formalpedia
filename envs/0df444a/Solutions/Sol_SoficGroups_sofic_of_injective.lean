-- Prove2me | solution 1 for SoficGroups.sofic_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/9e65dd04-3b7c-48c7-83fd-20746e22e510

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {G H : Type*} [Group G] [Group H]
    [Sofic G] (f : H →* G) (hf : Function.Injective f) : Sofic H := by
  classical
  constructor
  intro F ε hε hε'
  obtain ⟨M, hM⟩ := Sofic.approximation (F.image f) ε hε hε'
  let N : PermutationModel H :=
    { size := M.size
      size_pos := M.size_pos
      action := fun g => M.action (f g)
      map_one := by simpa using M.map_one }
  refine ⟨N, ?_⟩
  constructor
  · intro g hg h hh
    simpa [N] using hM.multiplicative
      (f g) (Finset.mem_image_of_mem f hg)
      (f h) (Finset.mem_image_of_mem f hh)
  · intro g hg hne
    apply hM.separated (f g) (Finset.mem_image_of_mem f hg)
    intro he
    apply hne
    apply hf
    simpa using he
end SoficGroups
