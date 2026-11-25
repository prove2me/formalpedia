-- Prove2me | solution 1 for P2M_PIW_ENSpec_forall__ofFn_a8a2da7e4e0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:33.225634+00:00
-- url     : https://prove2.me/submissions/e0278cd8-aa1d-4c97-a9e7-f1d6e677b920

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StSpecOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_WregOfSubsingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open PIW PIW.ENSpec
open MvPolynomial RingTheory.Sequence
open scoped Pointwise
variable {S : Type u} [CommRing S]
namespace PIW.ENSpec
theorem _root_.solution {α β : Type*} {P : α → β → Prop} :
    ∀ {n : ℕ} (f : Fin n → α) (g : Fin n → β), (∀ i, P (f i) (g i)) →
      List.Forall₂ P (List.ofFn f) (List.ofFn g)
  | 0, _, _, _ => by simp
  | n + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ]
    exact .cons (h 0) (solution _ _ fun i => h i.succ)
end PIW.ENSpec
