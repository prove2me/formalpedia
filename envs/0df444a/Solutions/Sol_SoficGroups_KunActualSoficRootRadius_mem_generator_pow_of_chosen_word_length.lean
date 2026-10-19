-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.mem_generator_pow_of_chosen_word_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/0cb0fc26-46ef-499b-a60a-479f5305031d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_generator_word_prod_mem_pow

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSoficRootRadius
open Filter Topology
open scoped BigOperators Pointwise
namespace SoficGroups.KunActualSoficRootRadius
theorem _root_.solution
    {G : Type*} [Group G] [DecidableEq G]
    (S : Finset G) (hone : 1 ∈ S)
    (w : G → List ↥S)
    (hw : ∀ g, ((w g).map fun i : ↥S => (i : G)).prod = g)
    {g : G} {r : ℕ} (hgr : (w g).length ≤ r) :
    g ∈ S ^ r := by
  have hword : g ∈ S ^ (w g).length := by
    simpa only [hw g] using generator_word_prod_mem_pow S (w g)
  exact Finset.pow_subset_pow_right hone hgr hword
end SoficGroups.KunActualSoficRootRadius
