-- Prove2me | solution 1 for ShannonColouring.card_misses_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:03:05.192683+00:00
-- url     : https://prove2.me/submissions/bc741bd1-5906-4bcf-b297-214ae6985057

module
public import Definitions.Def_ShannonColouring_Kempe
public import Definitions.Def_ShannonColouring_Shannon

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
open Classical
variable {V ι : Type*} [DecidableEq V] [Fintype ι]
omit [DecidableEq V] [Fintype ι]
namespace ShannonColouring
theorem _root_.solution {k : ℕ} (ends : ι → V × V) (s : Finset ι) (c : ι → Fin k) (x : V) :
    k ≤ (Finset.univ.filter (Misses ends s c x)).card +
      (s.filter fun i => Incident ends i x).card := by
  have hsub : (Finset.univ : Finset (Fin k)) ⊆
      Finset.univ.filter (Misses ends s c x) ∪ (s.filter fun i => Incident ends i x).image c := by
    intro δ _
    by_cases hδ : Misses ends s c x δ
    · exact Finset.mem_union_left _ (by simpa using hδ)
    · apply Finset.mem_union_right
      simp only [Misses, not_forall, not_not] at hδ
      obtain ⟨i, hi, hix, rfl⟩ := hδ
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hi, hix⟩)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at h1
  refine h1.trans ((Finset.card_union_le _ _).trans ?_)
  convert Nat.add_le_add_left Finset.card_image_le _ using 2
end ShannonColouring
