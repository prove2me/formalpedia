-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:09:49.20884+00:00
-- url     : https://prove2.me/submissions/37cf3171-068b-46a4-a36b-8cb15f120ac7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KrullDimQuotientEqOneIffEqBot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_krullDimLE_one_of_krullDim_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_krullDim_quotient_eq_one_iff_eq_bot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_coker_ne_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_ker_eq_zero_of_torsionFree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_localization_bot_eq_finrank
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ordQuotient_bot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_dimOneFormula


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution : LocalLengthAdditivityTorsionFree := by
  intro A _ _ _ _ M _ _ _ _ x h hx
  haveI : Ring.KrullDimLE 1 A := krullDimLE_one_of_krullDim_eq h
  obtain ⟨-, heq⟩ := dimOneFormula A M x h (length_coker_ne_top M hx)
  rw [heq, length_ker_eq_zero_of_torsionFree M hx, zero_add]
  have hset : {p : PrimeSpectrum A | ringKrullDim (A ⧸ p.asIdeal) = 1} = {⟨⊥, Ideal.isPrime_bot⟩} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [krullDim_quotient_eq_one_iff_eq_bot h p]
    constructor
    · intro hp
      ext1
      exact hp
    · intro hp
      rw [hp]
  change ∑ᶠ p ∈ {p : PrimeSpectrum A | ringKrullDim (A ⧸ p.asIdeal) = 1}, _ = _
  rw [hset, finsum_mem_singleton]
  dsimp only
  rw [length_localization_bot_eq_finrank, ordQuotient_bot]
end ReciprocityTheory.ChartRestriction.G.AI
