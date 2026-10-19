-- Prove2me | solution 1 for SoficGroups.exists_soficApproximation_size_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/45fde50d-552c-40e2-a66d-964fe39ce52b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_nonempty_soficApproximation_of_sofic
import Theorems.Thm_SoficGroups_amplifyApproximation_size_tendsto

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    (G : Type*) [Group G] [Countable G] [Sofic G] :
    ∃ A : SoficApproximation G,
      Tendsto (fun n => (A.model n).size) atTop atTop := by
  obtain ⟨A⟩ := nonempty_soficApproximation_of_sofic G
  exact ⟨amplifyApproximation A, amplifyApproximation_size_tendsto A⟩
end SoficGroups
