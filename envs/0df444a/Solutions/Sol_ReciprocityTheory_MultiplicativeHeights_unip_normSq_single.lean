-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.unip_normSq_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:11.4168+00:00
-- url     : https://prove2.me/submissions/53df099c-0542-417c-94a6-beb0696a171a

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {r : ℕ} (j : Fin r) : normSq (Pi.single j (1 : ℂ)) = 1 := by
  unfold normSq
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ j) h
end ReciprocityTheory.MultiplicativeHeights
