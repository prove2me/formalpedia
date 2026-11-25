-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.mid_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:49:14.012656+00:00
-- url     : https://prove2.me/submissions/e2edb30b-e346-46b2-92f5-3f8d4cb1dd1d

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (m : ℕ)
    (Lp : Submodule (𝓞 K) (Fin r → K)) :
    ∀ x ∈ (Lp ⊓ cutSub K r (r - m)).map (projGe K r m), ∀ a : Fin r,
      ((a : ℕ) < m ∨ r ≤ (a : ℕ) + m) → x a = 0 := by
  rintro _ ⟨y, ⟨_, hy⟩, rfl⟩ a ha
  show (if m ≤ (a : ℕ) then y a else 0) = 0
  split_ifs with h
  · exact hy a (by omega)
  · rfl
end ReciprocityTheory.MultiplicativeHeights.SemiPt
