-- Prove2me | solution 1 for UlmsTheorem.ulm_theorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:06:22.432169+00:00
-- url     : https://prove2.me/submissions/54b343cd-63fa-49fa-b81c-28d554202d77

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Classification
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Invariance
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Theorem
public import Theorems.Thm_UlmsTheorem_ulm_invariants_of_iso
public import Theorems.Thm_UlmsTheorem_iso_of_ulm_invariants

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Cardinal Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
namespace UlmsTheorem
theorem _root_.solution {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    (hGred : IsReducedPGroup p G) (hHred : IsReducedPGroup p H) :
    Nonempty (G ≃+ H) ↔
    ∀ α : Ordinal.{0},
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H) := by
  constructor
  · exact ulm_invariants_of_iso (p := p)
  · exact iso_of_ulm_invariants (p := p) hGred hHred
end UlmsTheorem
