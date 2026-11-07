-- Prove2me | solution 1 for UAVariety.satisfies_iff_hom
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T17:30:37.029529+00:00
-- url     : https://prove2.me/submissions/cf879d5a-b673-40c8-be51-be0d20a091d6

import Definitions.Def_UAVariety_defs

universe u₁ v₁

set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic]

theorem fid_satisfies_iff_hom {X : Type*} (A : Alg L) (p q : L.Term X) :
    Satisfies A (p, q) ↔ ∀ h : L.Term X →[L] A, h p = h q := by
  have key : ∀ (h : L.Term X →[L] A) (t : L.Term X), h t = t.realize (fun x => h (Term.var x)) := by
    intro h t
    induction t with
    | var x => rfl
    | func f ts ih =>
      show h (Structure.funMap f ts) = _
      rw [Hom.map_fun]
      simp only [Term.realize]
      congr 1
      funext i
      exact ih i
  constructor
  · intro hs h
    rw [key h p, key h q]
    exact hs _
  · intro hh v
    let e : L.Term X →[L] A := ⟨fun t => t.realize v, fun f ts => rfl, fun r => isEmptyElim r⟩
    exact hh e

end UAVariety

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] {X : Type*} (A : UAVariety.Alg L) (p q : L.Term X) :
    UAVariety.Satisfies A (p, q) ↔ ∀ h : L.Term X →[L] A, h p = h q :=
  UAVariety.fid_satisfies_iff_hom A p q
