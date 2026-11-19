-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCheck24
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T10:11:07.711426+00:00
-- url     : https://prove2.me/submissions/7a4de7c7-19d6-4c2f-9bae-603e3ffdebeb

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeDiagramRegionsChecked24

section
-- module Solutions.OAIQ259_US.Saxl_HorizontalRemoval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma rowPrefix_mono (μ : YoungDiagram) {k l : ℕ} (h : k ≤ l) :
    rowPrefix μ k ≤ rowPrefix μ l :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_RegionExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Region Exhaustion. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma boundsEntail_sound {A B : List (ℕ × ℕ)} (h : boundsEntail A B)
    (μ : YoungDiagram) (ha : RowBounds μ A) : RowBounds μ B := by
  intro p hp
  obtain ⟨hpos,q,hq,hk,hv⟩ := h p hp
  exact ⟨hpos,((rowPrefix_mono μ hk).trans (ha q hq).2).trans hv⟩

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeCover24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Cover 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover24_0_0 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 1 1 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_0_1 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 1 2 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_0_2 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 1 3 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_0_3 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 1 4 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_0_4 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 1 5 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_1_0 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 2 1 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_1_1 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 2 2 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_1_2 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 2 3 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_1_3 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 2 4 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_1_4 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 2 5 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_2_0 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 3 1 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_2_1 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 3 2 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_2_2 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 3 3 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_2_3 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 3 4 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_2_4 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 3 5 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_3_0 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 4 1 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_3_1 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 4 2 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_3_2 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 4 3 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_3_3 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 4 4 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_3_4 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 4 5 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_4_0 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 5 1 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_4_1 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 5 2 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_4_2 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 5 3 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_4_3 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 5 4 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_4_4 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 5 5 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 (d+1) (e+1) (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCover24_0_0
  · exact degreeCover24_0_1
  · exact degreeCover24_0_2
  · exact degreeCover24_0_3
  · exact degreeCover24_0_4
  · exact degreeCover24_1_0
  · exact degreeCover24_1_1
  · exact degreeCover24_1_2
  · exact degreeCover24_1_3
  · exact degreeCover24_1_4
  · exact degreeCover24_2_0
  · exact degreeCover24_2_1
  · exact degreeCover24_2_2
  · exact degreeCover24_2_3
  · exact degreeCover24_2_4
  · exact degreeCover24_3_0
  · exact degreeCover24_3_1
  · exact degreeCover24_3_2
  · exact degreeCover24_3_3
  · exact degreeCover24_3_4
  · exact degreeCover24_4_0
  · exact degreeCover24_4_1
  · exact degreeCover24_4_2
  · exact degreeCover24_4_3
  · exact degreeCover24_4_4

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_SymmetricRegions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric Regions. -/

section

namespace UniversalTensorSquare

lemma regionCheck_sound_diagram {n M r d e a b : ℕ} {q : List ℕ}
    {regions : List PrefixRegion} {P : List ℕ → Prop}
    (hc : ∀ R ∈ regions, ∀ μ : YoungDiagram, μ.card = n →
      RowBounds μ.transpose R.1 → RowBounds μ R.2 → P μ.rowLens)
    (h : regionCheck n M r d e a b q regions) :
    semanticResidualCheck n M r d e a b q P := by
  rcases h with h | h | h | ⟨R,hR,hA,hB⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · refine Or.inr (Or.inr (Or.inr ?_))
    intro μ hμ ha hb
    exact hc R hR μ hμ (boundsEntail_sound hA _ ha) (boundsEntail_sound hB _ hb)

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeChecks24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Checks 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck24_oai : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      semanticResidualCheck 24 4 7 (d+1) (e+1) (a+1) (c+1) degreeRows24_0 degreeP24 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked24 (degreeCover24 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCheck24_oai := @OAI.UniversalTensorSquare.degreeCheck24_oai
