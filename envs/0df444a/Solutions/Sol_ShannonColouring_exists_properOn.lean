-- Prove2me | solution 1 for ShannonColouring.exists_properOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:46:29.680946+00:00
-- url     : https://prove2.me/submissions/79c79f8f-f884-4198-808d-61250bf6079d

module
public import Definitions.Def_ShannonColouring_Kempe
public import Definitions.Def_ShannonColouring_Shannon
public import Theorems.Thm_ShannonColouring_card_incident_lt
public import Theorems.Thm_ShannonColouring_exists_properOn_insert

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
open Classical
variable {V ι : Type*} [DecidableEq V] [Fintype ι]
namespace ShannonColouring
theorem _root_.solution [Fintype V] {ends : ι → V × V} (hloop : ∀ i, (ends i).1 ≠ (ends i).2) (Δ : ℕ)
    (hΔ : ∀ v, degree ends v ≤ Δ) (s : Finset ι) :
    ∃ c : ι → Fin (3 * Δ / 2), ProperOn ends s c := by
  induction s using Finset.induction_on with
  | empty =>
    by_cases hι : IsEmpty ι
    · exact ⟨isEmptyElim, fun i => isEmptyElim i⟩
    · obtain ⟨i⟩ := not_isEmpty_iff.mp hι
      have h1 := card_incident_lt ends (Finset.notMem_empty i) (x := (ends i).1) (Or.inl rfl)
      have h2 := hΔ (ends i).1
      exact ⟨fun _ => ⟨0, by omega⟩, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert e s he ih =>
    obtain ⟨c, hc⟩ := ih
    exact exists_properOn_insert hloop hΔ (by omega) he hc
end ShannonColouring
