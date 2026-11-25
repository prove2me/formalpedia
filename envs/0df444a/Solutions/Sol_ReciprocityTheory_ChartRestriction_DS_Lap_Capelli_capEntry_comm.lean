-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capEntry_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:13:41.233906+00:00
-- url     : https://prove2.me/submissions/5769448f-e5e4-4e42-8ecb-edc0fc7d5331

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ProdOfFnUpdateEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution (hE : GlRelR E) (a b c d : Fin n) (x : ℂ) :
    E a b * capEntry E x c d - capEntry E x c d * E a b =
      (if b = c then capEntry E x a d else 0) - (if d = a then capEntry E x c b else 0) := by
  have hz : ∀ s : 𝒰, (s = 0 ∨ ∃ z : ℂ, s = algebraMap ℂ 𝒰 z) → E a b * s - s * E a b = 0 := by
    rintro s (rfl | ⟨z, rfl⟩)
    · simp
    · rw [Algebra.commutes, sub_self]
  have key : E a b * capEntry E x c d - capEntry E x c d * E a b =
      (E a b * E c d - E c d * E a b) + (E a b * (if c = d then algebraMap ℂ 𝒰 x else 0) -
        (if c = d then algebraMap ℂ 𝒰 x else 0) * E a b) := by
    unfold capEntry
    noncomm_ring
  have hs : (if c = d then algebraMap ℂ 𝒰 x else 0) = 0 ∨
      ∃ z : ℂ, (if c = d then algebraMap ℂ 𝒰 x else 0) = algebraMap ℂ 𝒰 z := by
    split_ifs
    · exact Or.inr ⟨x, rfl⟩
    · exact Or.inl rfl
  rw [key, hz _ hs, add_zero, hE a b c d]
  unfold capEntry
  split_ifs <;> subst_vars <;> first | rfl | simp_all | abel
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
