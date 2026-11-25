-- Prove2me | solution 1 for ReciprocityTheory.Cheb.sign_add_of_abs_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:45:21.255116+00:00
-- url     : https://prove2.me/submissions/7ee10dd8-c614-436e-8f58-30d4825c4ed8

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution {a e : ℝ} (h : |e| < |a|) : SignType.sign (a + e) = SignType.sign a := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [abs_of_neg ha] at h
    have : a + e < 0 := by linarith [le_abs_self e]
    rw [sign_neg this, sign_neg ha]
  · subst ha; simp at h; linarith [abs_nonneg e]
  · rw [abs_of_pos ha] at h
    have : 0 < a + e := by linarith [neg_abs_le e]
    rw [sign_pos this, sign_pos ha]
end ReciprocityTheory.Cheb
