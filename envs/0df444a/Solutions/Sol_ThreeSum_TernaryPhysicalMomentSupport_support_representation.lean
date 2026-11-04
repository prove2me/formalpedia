-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalMomentSupport.support_representation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:38:07.2429+00:00
-- url     : https://prove2.me/submissions/ff4095c8-d22b-42bd-8751-a5196d9fa6fb

import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Mathlib.Data.Finset.Sort
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalMomentSupport
import Theorems.Thm_ThreeSum_TernaryPhysicalMomentSupport_values_injective
import Theorems.Thm_ThreeSum_TernaryPhysicalMomentSupport_weights_positive
import Theorems.Thm_ThreeSum_TernaryPhysicalMomentSupport_grouped_moment
import Theorems.Thm_ThreeSum_TernaryPhysicalMomentSupport_target_iff

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalMomentSupport
open Finset FiniteMomentZeroDetector
open scoped BigOperators
variable {P : Type*} [Fintype P]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryPhysicalMomentSupport
theorem _root_.solution (mode mass : P → ℤ) (hm : ∀ a, 0<mass a)
    {H : ℕ} (hH : (support mode).card≤H) :
    ∃ t≤H, ∃ v w : Fin t → ℤ, Function.Injective v ∧
      (∀ i, w i≠0) ∧ (∀ k, moment v w k=∑ a, mass a*mode a^k) ∧
      (∀ target, (∃ i, v i=target) ↔ ∃ a, mode a=target) := by
  refine ⟨(support mode).card,hH,values mode,weights mode mass,values_injective mode,?_,
    grouped_moment mode mass,target_iff mode⟩
  intro i
  exact ne_of_gt (weights_positive mode mass hm i)
end ThreeSum.TernaryPhysicalMomentSupport
