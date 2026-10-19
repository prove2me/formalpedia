-- Prove2me | solution 1 for SoficGroups.exists_finitelyPresented_not_sofic_of_not_sofic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/ac4b939e-7b56-4d9a-ab5f-fec68ad19024

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_exists_nonsofic_finite_table

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {G : Type u} [Group G] (hG : ¬ Sofic G) :
    ∃ (H : Type u) (_ : Group H),
      Group.IsFinitelyPresented H ∧ ¬ Sofic H := by
  obtain ⟨F, h₁, hfp, hn⟩ := exists_nonsofic_finite_table hG
  exact ⟨tableGroup F h₁, inferInstance, hfp, hn⟩
end SoficGroups
