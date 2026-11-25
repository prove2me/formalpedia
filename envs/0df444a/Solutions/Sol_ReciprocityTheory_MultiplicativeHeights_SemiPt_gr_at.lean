-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.gr_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:55:23.692613+00:00
-- url     : https://prove2.me/submissions/dd0e839a-1045-4d64-8328-5f402e9cf6e8

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegN
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (Lp : Submodule (𝓞 K) (Fin r → K))
    (j : Fin r) : ∀ x ∈ (Lp ⊓ cutSub K r (j + 1)).map (projGe K r j), IsAt j x := by
  rintro _ ⟨y, ⟨_, hy⟩, rfl⟩ a ha
  show (if (j : ℕ) ≤ a then y a else 0) = 0
  split_ifs with h
  · exact hy a (by have : (a : ℕ) ≠ j := fun e => ha (Fin.ext e); omega)
  · rfl
end ReciprocityTheory.MultiplicativeHeights.SemiPt
