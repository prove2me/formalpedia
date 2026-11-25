-- Prove2me | solution 1 for ShannonColouring.ProperOn.extend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:20:53.507941+00:00
-- url     : https://prove2.me/submissions/88a29bd8-543e-41d2-8b6e-4b41cbfc02a2

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
namespace ProperOn
theorem _root_.solution [DecidableEq ι] {s : Finset ι} {c : ι → Fin k} (h : ProperOn ends s c) {e : ι}
    (he : e ∉ s) {δ : Fin k} (h1 : Misses ends s c (ends e).1 δ)
    (h2 : Misses ends s c (ends e).2 δ) : ProperOn ends (insert e s) (Function.update c e δ) := by
  have hm : ∀ j ∈ s, (∃ v, Incident ends e v ∧ Incident ends j v) → c j ≠ δ := by
    rintro j hj ⟨v, hev, hjv⟩
    rcases hev with rfl | rfl
    · exact h1 j hj hjv
    · exact h2 j hj hjv
  intro i hi j hj hij hv
  rw [Finset.mem_insert] at hi hj
  rcases hi with rfl | hi <;> rcases hj with rfl | hj
  · exact absurd rfl hij
  · have hje : j ≠ i := fun h => he (h ▸ hj)
    simp only [Function.update_self, Function.update_of_ne hje]
    exact (hm j hj hv).symm
  · have hie : i ≠ j := fun h => he (h ▸ hi)
    simp only [Function.update_self, Function.update_of_ne hie]
    obtain ⟨v, h1, h2⟩ := hv
    exact hm i hi ⟨v, h2, h1⟩
  · have hie : i ≠ e := fun h => he (h ▸ hi)
    have hje : j ≠ e := fun h => he (h ▸ hj)
    simp only [Function.update_of_ne hie, Function.update_of_ne hje]
    exact h i hi j hj hij hv
end ProperOn
end ShannonColouring
