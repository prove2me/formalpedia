-- Prove2me | solution 1 for UlmsTheorem.ulm_invariants_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:59:27.818184+00:00
-- url     : https://prove2.me/submissions/a1c54f11-3e5e-448e-ba60-c37118b90c30

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Classification
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Invariance
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Theorem
public import Theorems.Thm_UlmsTheorem_ulmInvariant_iso_invariant


set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Cardinal Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
namespace UlmsTheorem
theorem _root_.solution {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (hiso : Nonempty (G ≃+ H)) :
    ∀ α : Ordinal.{0},
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H) := by
  rcases hiso with ⟨φ⟩
  intro α
  exact ulmInvariant_iso_invariant (p := p) φ α
end UlmsTheorem
