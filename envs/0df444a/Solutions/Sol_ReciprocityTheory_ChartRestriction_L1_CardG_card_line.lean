-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.CardG.card_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:33:58.080201+00:00
-- url     : https://prove2.me/submissions/3d922637-555e-4571-88fc-0e859b0fa7a5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedHalf
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedCardG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open ReciprocityTheory.ChartRestriction.L1.CardG
namespace ReciprocityTheory.ChartRestriction.L1.CardG
theorem _root_.solution {F : Type} [Field F] [Fintype F] (u v : F) (h : u ≠ 0 ∨ v ≠ 0) :
    (Finset.univ.filter (fun w : F × F => u * w.1 + v * w.2 = 0)).card = Fintype.card F := by
  rcases h with h | h
  · have : Finset.univ.filter (fun w : F × F => u * w.1 + v * w.2 = 0)
        = Finset.univ.image (fun t : F => (-(v * t) / u, t)) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
      constructor
      · intro e
        refine ⟨y, ?_, rfl⟩
        field_simp
        linear_combination -e
      · rintro ⟨t, e, rfl⟩
        rw [← e]; field_simp; ring
    rw [this, Finset.card_image_of_injective _ (fun s t e => (Prod.mk.inj e).2), Finset.card_univ]
  · have : Finset.univ.filter (fun w : F × F => u * w.1 + v * w.2 = 0)
        = Finset.univ.image (fun t : F => (t, -(u * t) / v)) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
      constructor
      · intro e
        refine ⟨x, rfl, ?_⟩
        field_simp
        linear_combination -e
      · rintro ⟨t, rfl, e⟩
        rw [← e]; field_simp; ring
    rw [this, Finset.card_image_of_injective _ (fun s t e => (Prod.mk.inj e).1), Finset.card_univ]
end ReciprocityTheory.ChartRestriction.L1.CardG
