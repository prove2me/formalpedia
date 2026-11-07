-- Prove2me | solution 1 for UAVariety.free_identities
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T17:30:39.992669+00:00
-- url     : https://prove2.me/submissions/5fd9c944-0dec-4ea0-8c99-fc00b0374627

import Definitions.Def_UAVariety_defs
import Theorems.Thm_UAVariety_same_identities
import Theorems.Thm_UAVariety_ker_quot_mem_S
import Theorems.Thm_UAVariety_free_mem_SP
import Theorems.Thm_UAVariety_satisfies_iff_hom
import Theorems.Thm_UAVariety_realize_quot_var

universe u₁ v₁

set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic]

theorem fid_main (K : Set (Alg L)) (X : Type u₁) (p q : L.Term X) :
    ((∀ A ∈ K, Satisfies A (p, q)) ↔ Satisfies (freeAlg K X) (p, q)) ∧
      (Satisfies (freeAlg K X) (p, q) ↔ freeMk K X p = freeMk K X q) ∧
      (freeMk K X p = freeMk K X q ↔ (freeCong K X).r p q) := by
  have hD : freeMk K X p = freeMk K X q ↔ (freeCong K X).r p q :=
    ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩
  have hA : (freeCong K X).r p q → ∀ A ∈ K, Satisfies A (p, q) := by
    intro hθ A hA
    rw [satisfies_iff_hom]
    intro h
    obtain ⟨φ, hφ, hmem⟩ := ker_quot_mem_S K hA h
    exact (hφ p q).1 (hθ φ hmem)
  have hB : (∀ A ∈ K, Satisfies A (p, q)) → Satisfies (freeAlg K X) (p, q) := by
    intro hK
    have hP := (same_identities K p q).2.2.1.2 hK
    exact (same_identities (P K) p q).2.1.2 hP _ (free_mem_SP K X).1
  have hC : Satisfies (freeAlg K X) (p, q) → freeMk K X p = freeMk K X q := by
    intro h
    have h' := h (fun x => (Quotient.mk (freeCong K X).toSetoid (Term.var x) : (freeCong K X).Quot))
    have e1 := realize_quot_var (freeCong K X) p
    have e2 := realize_quot_var (freeCong K X) q
    exact e1.symm.trans (h'.trans e2)
  exact ⟨⟨hB, fun h => hA (hD.1 (hC h))⟩, ⟨hC, fun h => hB (hA (hD.1 h))⟩, hD⟩

end UAVariety

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] (K : Set (UAVariety.Alg L)) (X : Type u₁) (p q : L.Term X) :
    ((∀ A ∈ K, UAVariety.Satisfies A (p, q)) ↔ UAVariety.Satisfies (UAVariety.freeAlg K X) (p, q)) ∧
      (UAVariety.Satisfies (UAVariety.freeAlg K X) (p, q) ↔ UAVariety.freeMk K X p = UAVariety.freeMk K X q) ∧
      (UAVariety.freeMk K X p = UAVariety.freeMk K X q ↔ (UAVariety.freeCong K X).r p q) :=
  UAVariety.fid_main K X p q
