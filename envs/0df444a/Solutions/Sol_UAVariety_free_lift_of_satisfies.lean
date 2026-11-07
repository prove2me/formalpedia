-- Prove2me | solution 1 for UAVariety.free_lift_of_satisfies
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T17:47:07.963691+00:00
-- url     : https://prove2.me/submissions/ca5f1c83-2bd5-4d53-90ec-dae8d5f09e7d

import Definitions.Def_UAVariety_defs
import Theorems.Thm_UAVariety_term_ump
import Theorems.Thm_UAVariety_quot_lift_hom
import Theorems.Thm_UAVariety_satisfies_iff_hom
import Theorems.Thm_UAVariety_free_identities

universe u₁ v₁

set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic]

theorem bh_free_lift (K : Set (Alg L)) (X : Type u₁) (A : Alg L) (v : X → A)
    (hA : ∀ p q : L.Term X, (∀ B ∈ K, Satisfies B (p, q)) → Satisfies A (p, q)) :
    ∃ f : freeAlg K X →[L] A, ∀ x, f (freeGen K X x) = v x := by
  obtain ⟨h, hv, -⟩ := term_ump (L := L) (A := A) v
  have hker : ∀ p q, (freeCong K X).r p q → h p = h q := by
    intro p q hpq
    have hfi := free_identities K X p q
    have hK : ∀ B ∈ K, Satisfies B (p, q) := hfi.1.2 (hfi.2.1.2 (hfi.2.2.2 hpq))
    exact (satisfies_iff_hom A p q).1 (hA p q hK) h
  obtain ⟨g, hg⟩ := quot_lift_hom (freeCong K X) h hker
  exact ⟨g, fun x => (hg (Term.var x)).trans (hv x)⟩

end UAVariety

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] (K : Set (UAVariety.Alg L)) (X : Type u₁) (A : UAVariety.Alg L) (v : X → A)
    (hA : ∀ p q : L.Term X, (∀ B ∈ K, UAVariety.Satisfies B (p, q)) → UAVariety.Satisfies A (p, q)) :
    ∃ f : UAVariety.freeAlg K X →[L] A, ∀ x, f (UAVariety.freeGen K X x) = v x :=
  UAVariety.bh_free_lift K X A v hA
