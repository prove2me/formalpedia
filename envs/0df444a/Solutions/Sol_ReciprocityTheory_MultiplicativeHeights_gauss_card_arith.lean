-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gauss_card_arith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:35:05.225002+00:00
-- url     : https://prove2.me/submissions/eefedc1f-f051-4780-8d66-b7ef15eb18dd

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussIndepOfLeTrdeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {a b : Cardinal} {s d : ℕ} (h : ((s + d : ℕ) : Cardinal) ≤ a + b)
    (ha : a ≤ d) (hb : b ≤ s) : a = d ∧ b = s := by
  obtain ⟨a', rfl⟩ := Cardinal.lt_aleph0.1 (ha.trans_lt (Cardinal.nat_lt_aleph0 d))
  obtain ⟨b', rfl⟩ := Cardinal.lt_aleph0.1 (hb.trans_lt (Cardinal.nat_lt_aleph0 s))
  have h' : s + d ≤ a' + b' := by exact_mod_cast h
  have ha' : a' ≤ d := by exact_mod_cast ha
  have hb' : b' ≤ s := by exact_mod_cast hb
  constructor
  · exact_mod_cast (by omega : a' = d)
  · exact_mod_cast (by omega : b' = s)
end ReciprocityTheory.MultiplicativeHeights
