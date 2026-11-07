-- Prove2me | solution 1 for UAVariety.realize_quot_var
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T17:30:38.296976+00:00
-- url     : https://prove2.me/submissions/e30fd1b3-41b7-4eb7-9dc1-304fb8cdcd2a

import Definitions.Def_UAVariety_defs

universe u₁ v₁

set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic]

theorem fid_realize_quot_var {X : Type*} (φ : Congruence (L := L) (L.Term X)) (p : L.Term X) :
    p.realize (fun x => (Quotient.mk φ.toSetoid (Term.var x) : φ.Quot)) =
      Quotient.mk φ.toSetoid p := by
  induction p with
  | var x => rfl
  | func f ts ih =>
    simp only [Term.realize]
    rw [show (fun i => (ts i).realize fun x => (Quotient.mk φ.toSetoid (Term.var x) : φ.Quot))
        = fun i => Quotient.mk φ.toSetoid (ts i) from funext ih]
    rw [funMap_quotient_mk']
    rfl

end UAVariety

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] {X : Type*} (φ : UAVariety.Congruence (L := L) (L.Term X)) (p : L.Term X) :
    p.realize (fun x => (Quotient.mk φ.toSetoid (Term.var x) : φ.Quot)) =
      Quotient.mk φ.toSetoid p :=
  UAVariety.fid_realize_quot_var φ p
