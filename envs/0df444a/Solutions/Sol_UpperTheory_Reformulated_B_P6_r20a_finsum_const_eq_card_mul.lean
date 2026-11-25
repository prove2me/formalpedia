-- Prove2me | solution 1 for UpperTheory.Reformulated.B.P6.r20a.finsum_const_eq_card_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:46:48.645809+00:00
-- url     : https://prove2.me/submissions/e0af6b0a-6872-42cd-961b-58421d39982e

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_QuotientOutRightInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r20a
namespace UpperTheory.Reformulated.B.P6.r20a
theorem _root_.solution {α : Type} [Finite α] (c : ℂ) : ∑ᶠ _ : α, c = (Nat.card α : ℂ) * c := by
  haveI : Fintype α := Fintype.ofFinite α
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
end UpperTheory.Reformulated.B.P6.r20a
