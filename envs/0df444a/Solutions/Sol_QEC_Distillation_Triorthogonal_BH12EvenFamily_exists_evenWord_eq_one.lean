-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12EvenFamily.exists_evenWord_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:37:27.983636+00:00
-- url     : https://prove2.me/submissions/e0c24afc-62a4-4ce6-b58c-903115dc61a8

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.Triorthogonal.BH12EvenFamily
theorem _root_.solution {q : Nat} (j : Column q) :
    ∃ r : EvenRow, evenWord r j = 1 := by
  rcases j with c | c
  · fin_cases c
    · exact ⟨2, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
  · rcases c with c | c
    · fin_cases c
      · exact ⟨2, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
    · rcases c with ⟨i, c⟩
      fin_cases c
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
end QEC.Distillation.Triorthogonal.BH12EvenFamily
