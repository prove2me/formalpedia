-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.chiAt_of_U
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:11:27.292055+00:00
-- url     : https://prove2.me/submissions/994c8bb0-f096-4496-b9b4-bbacf2233262

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_theta_sq_red

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} (h : ChiAtU g γ) :
    ChiAt g γ := by
  intro n n'
  obtain ⟨k, k', c, hc, h⟩ := h n n'
  refine ⟨fun i => k i % 2, fun i => k' i % 2, c, fun i => Int.emod_two_eq_zero_or_one _,
    fun i => Int.emod_two_eq_zero_or_one _, hc, ?_⟩
  intro τ hτ z
  rw [← theta_sq_red]
  exact h τ hτ z
end ReciprocityTheory.ChartRestriction.G.Key.Chi
