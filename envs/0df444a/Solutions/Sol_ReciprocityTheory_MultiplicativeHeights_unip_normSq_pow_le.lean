-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.unip_normSq_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:17:50.343971+00:00
-- url     : https://prove2.me/submissions/b43bd421-721f-47ad-9381-bc6f3a113bf4

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
theorem _root_.solution {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ u, normSq (A *ᵥ u) ≤ c * normSq u) (n : ℕ) (u : Fin r → ℂ) :
    normSq ((A ^ n) *ᵥ u) ≤ c ^ n * normSq u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, pow_succ']
    calc normSq (A *ᵥ (A ^ n *ᵥ u)) ≤ c * normSq (A ^ n *ᵥ u) := hA _
      _ ≤ c * (c ^ n * normSq u) := mul_le_mul_of_nonneg_left ih hc
      _ = c * c ^ n * normSq u := by ring
end ReciprocityTheory.MultiplicativeHeights
