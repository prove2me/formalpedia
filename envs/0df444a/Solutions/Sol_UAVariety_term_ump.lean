-- Prove2me | solution 1 for UAVariety.term_ump
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T16:55:27.735201+00:00
-- url     : https://prove2.me/submissions/203f8015-cf2a-4b98-b44a-e5d689891f4a

import Definitions.Def_UAVariety_defs

universe u₁ v₁

set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic]

theorem fu_term_ump {X : Type*} {A : Type*} [L.Structure A] (v : X → A) :
    ∃! h : L.Term X →[L] A, ∀ x, h (Term.var x) = v x := by
  refine ⟨⟨fun p => p.realize v, fun f ts => rfl, fun r => isEmptyElim r⟩, fun x => rfl, ?_⟩
  intro g hg
  ext p
  induction p with
  | var x => exact hg x
  | func f ts ih =>
    show g (Structure.funMap f ts) = _
    rw [g.map_fun]
    show _ = Structure.funMap f (fun i => (ts i).realize v)
    congr 1; funext i; exact ih i


end UAVariety

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] {X : Type*} {A : Type*} [L.Structure A] (v : X → A) :
    ∃! h : L.Term X →[L] A, ∀ x, h (Term.var x) = v x :=
  UAVariety.fu_term_ump v
