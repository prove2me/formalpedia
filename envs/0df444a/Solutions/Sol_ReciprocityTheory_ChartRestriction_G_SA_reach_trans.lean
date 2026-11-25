-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.reach_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:55:43.09132+00:00
-- url     : https://prove2.me/submissions/cf4c2afe-dfb8-4859-a555-c62eaeb4771c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ConjMemEichSet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ReachableFixingAddSmulSecond
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_good_mul


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
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {b b' b'' : ι → K} (h1 : Reach σ J e f a b b') (h2 : Reach σ J e f a b' b'') :
    Reach σ J e f a b b'' := by
  obtain ⟨p1, hp1, ha1, hb1⟩ := h1
  obtain ⟨p2, hp2, ha2, hb2⟩ := h2
  refine ⟨p2 * p1, (by apply good_mul <;> assumption), fun j => ?_, ?_⟩
  · rw [← Matrix.mulVec_mulVec, ha1, ha2]
  · rw [← Matrix.mulVec_mulVec, hb1, hb2]
end ReciprocityTheory.ChartRestriction.G.SA
