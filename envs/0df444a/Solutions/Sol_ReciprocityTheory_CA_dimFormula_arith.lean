-- Prove2me | solution 1 for ReciprocityTheory.CA.dimFormula_arith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:10:07.599772+00:00
-- url     : https://prove2.me/submissions/28c03e21-fda1-4cdc-9ec1-4b0aceb78132

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_RingKrullDimLocalizationQuotientEqHeight
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_DimFormulaOfSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing
namespace ReciprocityTheory.CA
theorem _root_.solution (a b : ℕ∞) (c d : WithBot ℕ∞) (n : ℕ) (hc : c ≠ ⊥) (hd : d ≠ ⊥)
    (h1 : ((a + b : ℕ∞) : WithBot ℕ∞) + c = n) (h2 : (a : WithBot ℕ∞) + d = n) :
    (b : WithBot ℕ∞) + c = d := by
  obtain ⟨c, rfl⟩ := WithBot.ne_bot_iff_exists.mp hc
  obtain ⟨d, rfl⟩ := WithBot.ne_bot_iff_exists.mp hd
  have e1 : a + b + c = (n : ℕ∞) := by exact_mod_cast h1
  have e2 : a + d = (n : ℕ∞) := by exact_mod_cast h2
  suffices e3 : b + c = d by exact_mod_cast e3
  induction a using ENat.recTopCoe with
  | top => simp at e2
  | coe a =>
    induction d using ENat.recTopCoe with
    | top => simp at e2
    | coe d =>
      induction b using ENat.recTopCoe with
      | top => simp at e1
      | coe b =>
        induction c using ENat.recTopCoe with
        | top => simp at e1
        | coe c =>
          norm_cast at e1 e2 ⊢
          omega
end ReciprocityTheory.CA
