-- Prove2me | solution 1 for Sendov.sumEraseProdMap_eq_esymm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:03:32.21739+00:00
-- url     : https://prove2.me/submissions/51bc6626-c509-4d3f-8524-c894ac5ad7fd

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
import Theorems.Thm_Sendov_sumEraseProdMap_cons
import Theorems.Thm_Sendov_esymm_card_cons
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution {α : Type*} : ∀ (s : Multiset α) (f : α → ℝ), s ≠ 0 →
    sumEraseProdMap s f = (s.map f).esymm ((s.map f).card - 1) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _ h; exact absurd rfl h
  | cons v t ih =>
    intro f _
    rcases eq_or_ne t 0 with rfl | ht
    · simp [sumEraseProdMap, Multiset.esymm]
    · rw [sumEraseProdMap_cons, ih f ht, Multiset.map_cons, Multiset.card_cons]
      rw [show (t.map f).card + 1 - 1 = (t.map f).card from by omega]
      rw [esymm_card_cons (f v) (t.map f) (by simpa using ht)]
end Sendov
