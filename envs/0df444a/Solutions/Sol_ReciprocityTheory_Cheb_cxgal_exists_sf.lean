-- Prove2me | solution 1 for ReciprocityTheory.Cheb.cxgal_exists_sf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:39.068742+00:00
-- url     : https://prove2.me/submissions/16a84cc5-4754-4f01-8b95-af405c7fe6db

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossGal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] :
    ∃ p : ℚ[X], p ≠ 0 ∧ IsSplittingField ℚ K p := by
  obtain ⟨p, hp⟩ := Normal.exists_isSplittingField ℚ K
  by_cases h0 : p = 0
  · subst h0
    refine ⟨X, X_ne_zero, ?_⟩
    constructor
    · simp
    · have h := hp.adjoin_rootSet
      simp only [rootSet_zero, Algebra.adjoin_empty] at h
      rw [eq_top_iff, ← h]
      exact bot_le
  · exact ⟨p, h0, hp⟩
end ReciprocityTheory.Cheb
