-- Prove2me | solution 1 for ThreeSum.TernaryCoverRegularity.same_type_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:10:24.706646+00:00
-- url     : https://prove2.me/submissions/15a3cd91-7e89-4859-990b-53047e9fbd07

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}
namespace ThreeSum.TernaryCoverRegularity
theorem _root_.solution {a b : TritWord L} {α : DigitType}
    (ha : HasType a α) (hb : HasType b α) :
    ∃ σ : Equiv.Perm (Fin L), reindex σ a = b := by
  classical
  have hc (d : Fin 3) : Fintype.card {i // b i = d} = Fintype.card {i // a i = d} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, card_filter, card_filter]
    change digitCount b d = digitCount a d
    rw [hb d, ha d]
  let e (d : Fin 3) : {i // b i = d} ≃ {i // a i = d} := Fintype.equivOfCardEq (hc d)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext i
  exact Equiv.ofFiberEquiv_map e i
end ThreeSum.TernaryCoverRegularity
