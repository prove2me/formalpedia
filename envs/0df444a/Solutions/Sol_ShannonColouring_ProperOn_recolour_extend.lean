-- Prove2me | solution 1 for ShannonColouring.ProperOn.recolour_extend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:34:36.958521+00:00
-- url     : https://prove2.me/submissions/d93bb870-193b-49e3-8e4d-85fc00b51e84

module
public import Definitions.Def_ShannonColouring_Defs
public import Definitions.Def_ShannonColouring_PathEnds
public import Definitions.Def_ShannonColouring_Kempe
public import Theorems.Thm_ShannonColouring_ProperOn_extend
public import Theorems.Thm_ShannonColouring_ProperOn_recolour

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
variable {V ι : Type*}
variable {ends : ι → V × V} {k : ℕ}
namespace ShannonColouring
namespace ProperOn
theorem _root_.solution [DecidableEq ι] {s : Finset ι} {c : ι → Fin k} (h : ProperOn ends s c) {e f : ι}
    (he : e ∉ s) (hf : f ∈ s) {α β : Fin k} (hfu : Incident ends f (ends e).1) (hcf : c f = β)
    (hα : ∀ x, Incident ends f x → Misses ends s c x α) (hβ : Misses ends s c (ends e).2 β) :
    ∃ c' : ι → Fin k, ProperOn ends (insert e s) c' := by
  have h1 := h.recolour hf hα
  refine ⟨_, h1.extend he (δ := β) ?_ ?_⟩
  · intro i hi hiu
    by_cases hif : i = f
    · subst hif
      rw [Function.update_self]
      intro hαβ
      exact hα _ hfu i hi hfu (hcf.trans hαβ.symm)
    · rw [Function.update_of_ne hif, ← hcf]
      exact h.ne_of_incident hi hf hif hiu hfu
  · intro i hi hiv
    by_cases hif : i = f
    · subst hif
      exact absurd hcf (hβ i hi hiv)
    · rw [Function.update_of_ne hif]
      exact hβ i hi hiv
end ProperOn
end ShannonColouring
