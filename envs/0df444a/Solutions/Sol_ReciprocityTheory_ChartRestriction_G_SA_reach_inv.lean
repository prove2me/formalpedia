-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.reach_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:55:32.588695+00:00
-- url     : https://prove2.me/submissions/b8738199-235c-4649-bafd-994b0100f3c7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ConjMemEichSet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ReachableFixingAddSmulSecond
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_good_preserves

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1) {s : ℕ} {a : Fin s → ι → K}
  (hae : ∀ j, hf σ J (a j) e = 0) (haf : ∀ j, hf σ J (a j) f = 0)
include hσ hJ he hff hef
include hae haf
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {b b' : ι → K} (h : Reach σ J e f a b b') (hb : ∀ j, hf σ J b (a j) = 0) :
    (∀ j, hf σ J b' (a j) = 0) ∧ hf σ J b' b' = hf σ J b b := by
  obtain ⟨p, hp, ha, rfl⟩ := h
  refine ⟨fun j => ?_, good_preserves hσ hJ he hff hef hae haf hp b b⟩
  rw [← ha j, good_preserves hσ hJ he hff hef hae haf hp, hb]
end ReciprocityTheory.ChartRestriction.G.SA
