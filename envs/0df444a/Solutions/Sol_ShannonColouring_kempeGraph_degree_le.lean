-- Prove2me | solution 1 for ShannonColouring.kempeGraph_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:13:58.44884+00:00
-- url     : https://prove2.me/submissions/cfde81de-e07a-4d38-9791-e63ad34bee74

module
public import Definitions.Def_ShannonColouring_Defs
public import Definitions.Def_ShannonColouring_PathEnds
public import Definitions.Def_ShannonColouring_Kempe

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
variable {V ι : Type*}
variable {ends : ι → V × V} {k : ℕ}
namespace ShannonColouring
theorem _root_.solution [Fintype V] {s : Finset ι} {c : ι → Fin k} (h : ProperOn ends s c)
    {α γ : Fin k} [DecidableRel (kempeGraph ends s c α γ).Adj] (x : V) (D : Finset (Fin k))
    (hD : ∀ i ∈ s, Incident ends i x → (c i = α ∨ c i = γ) → c i ∈ D) :
    (kempeGraph ends s c α γ).degree x ≤ D.card := by
  classical
  let E := s.filter fun i => Incident ends i x ∧ (c i = α ∨ c i = γ)
  let other : ι → V := fun i => if (ends i).1 = x then (ends i).2 else (ends i).1
  have hsub : (kempeGraph ends s c α γ).neighborFinset x ⊆ E.image other := by
    intro b hb
    rw [SimpleGraph.mem_neighborFinset] at hb
    obtain ⟨hxb, i, hi, hc, hends⟩ := hb
    rw [Finset.mem_image]
    refine ⟨i, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨hi, ?_, hc⟩
      simp only [Incident]
      rcases hends with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact Or.inl h1
      · exact Or.inr h2
    · simp only [other]
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp [h1, h2]
      · simp [h1, Ne.symm hxb]
  have hinj : Set.InjOn c E := by
    intro i hi j hj hij
    simp only [E, Finset.coe_filter, Set.mem_setOf_eq] at hi hj
    by_contra hne
    exact h.ne_of_incident hi.1 hj.1 hne hi.2.1 hj.2.1 hij
  have himg : E.image c ⊆ D := by
    intro d hd
    simp only [E, Finset.mem_image, Finset.mem_filter] at hd
    obtain ⟨i, ⟨hi, hix, hc⟩, rfl⟩ := hd
    exact hD i hi hix hc
  calc (kempeGraph ends s c α γ).degree x
      = ((kempeGraph ends s c α γ).neighborFinset x).card := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ (E.image other).card := Finset.card_le_card hsub
    _ ≤ E.card := Finset.card_image_le
    _ = (E.image c).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ D.card := Finset.card_le_card himg
end ShannonColouring
