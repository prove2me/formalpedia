-- Prove2me | solution 1 for SetCoverThreshold.SetCover.gapNPHard_of_reduction
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T19:45:18.759721+00:00
-- url     : https://prove2.me/submissions/b5e9bbb0-1ce4-4508-88ca-875e953cf9e3

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Theorems.Thm_CookPvsNP_polyTimeComputable_comp

set_option autoImplicit false
set_option linter.unusedVariables false

open SetCoverThreshold.SetCover

theorem solution {α β Sym₁ Sym₂ : Type}
    (enc₁ : α → List Sym₁) (Yes₁ No₁ : α → Prop)
    (enc₂ : β → List Sym₂) (Yes₂ No₂ : β → Prop)
    (h₁ : GapNPHard enc₁ Yes₁ No₁)
    (g : α → β) (g_enc : List Sym₁ → List Sym₂)
    (hg_poly : CookPvsNP.PolyTimeComputable g_enc)
    (hg_enc : ∀ a, (Yes₁ a ∨ No₁ a) → enc₂ (g a) = g_enc (enc₁ a))
    (hg_yes : ∀ a, Yes₁ a → Yes₂ (g a))
    (hg_no : ∀ a, No₁ a → No₂ (g a)) :
    GapNPHard enc₂ Yes₂ No₂ := by
  intro Sym' _ _ L' hL'
  obtain ⟨f, hf_poly, hf⟩ := h₁ Sym' L' hL'
  refine ⟨fun x => g (f x), ?_, fun x => ⟨fun hx => hg_yes (f x) ((hf x).1 hx), fun hx => hg_no (f x) ((hf x).2 hx)⟩⟩
  have hcomp : (fun x => enc₂ (g (f x))) = g_enc ∘ (fun x => enc₁ (f x)) := by
    funext x
    apply hg_enc (f x)
    by_cases hx : x ∈ L'
    · exact Or.inl ((hf x).1 hx)
    · exact Or.inr ((hf x).2 hx)
  rw [hcomp]
  exact CookPvsNP.polyTimeComputable_comp (fun x => enc₁ (f x)) g_enc hf_poly hg_poly
