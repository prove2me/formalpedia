-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCheck14
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:37:14.934786+00:00
-- url     : https://prove2.me/submissions/96ea1f84-d3cd-482e-83ea-973390e9064f

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkedRegion_diagram
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq

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
-- module Solutions.OAIQ259_US.UniversalSquare_Band_TwoStrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two Strip. -/

section

noncomputable section

namespace Saxl.Balance

lemma ofRowLens_height (A : List ℕ) (hA : A.SortedGE) :
    (YoungDiagram.ofRowLens A hA).colLen 0 ≤ A.length := by
  by_contra hh
  have h := YoungDiagram.mem_iff_lt_colLen.mpr
    (show A.length < (YoungDiagram.ofRowLens A hA).colLen 0 by omega)
  obtain ⟨h',_⟩ := YoungDiagram.mem_ofRowLens.mp h
  exact (Nat.lt_irrefl _) h'

lemma ofRowLens_rowLen (A : List ℕ) (hA : A.SortedGE) (i : ℕ) :
    (YoungDiagram.ofRowLens A hA).rowLen i = A[i]?.getD 0 := by
  by_cases hi : i < A.length
  · simpa [hi] using YoungDiagram.rowLen_ofRowLens (hw := hA) ⟨i,hi⟩
  · rw [rowLen_zero_of_height_le _ ((ofRowLens_height A hA).trans (by omega))]
    simp [List.getElem?_eq_none (by omega : A.length ≤ i)]

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ZeroColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zero Columns. -/

section

noncomputable section
namespace Saxl.Columns

lemma sum_fin_val_ite (r i : ℕ) :
    (∑ j : Fin r, if j.val = i then (1:ℕ) else 0) = if i < r then 1 else 0 := by
  classical
  by_cases hi : i < r
  · rw [ite_eq_left hi, Finset.sum_eq_single (⟨i,hi⟩ : Fin r)]
    · simp
    · intro j hj hji
      exact ite_eq_right (fun h => hji (Fin.ext h))
    · simp
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j hj
    exact ite_eq_right (fun h : (j : ℕ) = i => hi (h ▸ j.isLt))

lemma cells_row_count (rs : List ℕ) (i : ℕ) :
    (∑ c : Cells rs, if row c = i then (1:ℕ) else 0) = rs.countP (fun h => i < h) := by
  classical
  induction rs with
  | nil => simp [Cells]
  | cons h rs ih =>
    rw [show (∑ c : Cells (h :: rs), if row c = i then (1:ℕ) else 0) =
      (∑ c : Fin h, if c.val = i then (1:ℕ) else 0) +
        (∑ c : Cells rs, if row c = i then (1:ℕ) else 0) from
      Fintype.sum_sum_type _]
    rw [sum_fin_val_ite, ih, List.countP_cons]
    split_ifs <;> simp_all <;> omega

lemma placed_rowLen {rs : List ℕ} {μ : YoungDiagram} (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c) (i : ℕ) :
    μ.rowLen i = rs.countP (fun h => i < h) := by
  classical
  let E : {c : Cells rs // row c = i} ≃ {c : μ.cells // c.val.1 = i} :=
    e.subtypeEquiv (fun c => by rw [hr])
  have hc := Fintype.card_congr (E.trans (rowFiberEquiv μ i))
  rw [Fintype.card_fin, Fintype.card_subtype, Finset.card_filter, cells_row_count] at hc
  exact hc.symm

lemma columnShape_rowLen (rs : List ℕ) (i : ℕ) :
    (columnShape rs).rowLen i = rs.countP (fun h => i < h) := by
  obtain ⟨e,hr,_⟩ := columnShape_placement rs
  exact placed_rowLen e hr i

end Saxl.Columns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_RowCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Certificates. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma rowDiagram_rowLens (μ : YoungDiagram) : rowDiagram μ.rowLens = μ := by
  rw [rowDiagram_eq _ ⟨μ.rowLens_sorted,μ.pos_of_mem_rowLens⟩,
    YoungDiagram.ofRowLens_to_rowLens_eq_self]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_NumericalSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Support. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma headD_rowLens (μ : YoungDiagram) : μ.rowLens.headD 0 = μ.rowLen 0 := by
  have h (xs : List ℕ) : xs.headD 0 = xs[0]?.getD 0 := by cases xs <;> rfl
  rw [h, ← ofRowLens_rowLen μ.rowLens μ.rowLens_sorted,
    YoungDiagram.ofRowLens_to_rowLens_eq_self]

lemma transposeRows_rowLens (μ : YoungDiagram) :
    transposeRows μ.rowLens = μ.transpose.rowLens := by
  unfold transposeRows
  rw [headD_rowLens]
  conv_rhs => rw [YoungDiagram.rowLens,YoungDiagram.colLen_transpose]
  apply List.map_congr_left
  intro j _
  rw [YoungDiagram.rowLen_transpose]
  have he := congrArg (fun θ : YoungDiagram => θ.colLen j) (rowDiagram_rowLens μ)
  simpa only [rowDiagram,YoungDiagram.colLen_transpose,columnShape_rowLen] using he

end UniversalTensorSquare

end
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeCover14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Cover 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover14_0_0 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 1 1 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_0_1 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 1 2 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_0_2 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 1 3 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_0_3 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 1 4 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_0_4 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 1 5 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_1_0 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 2 1 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_1_1 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 2 2 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_1_2 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 2 3 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_1_3 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 2 4 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_1_4 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 2 5 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_2_0 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 3 1 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_2_1 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 3 2 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_2_2 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 3 3 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_2_3 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 3 4 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_2_4 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 3 5 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_3_0 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 4 1 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_3_1 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 4 2 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_3_2 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 4 3 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_3_3 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 4 4 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_3_4 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 4 5 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_4_0 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 5 1 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_4_1 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 5 2 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_4_2 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 5 3 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_4_3 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 5 4 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_4_4 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 5 5 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 (d+1) (e+1) (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCover14_0_0
  · exact degreeCover14_0_1
  · exact degreeCover14_0_2
  · exact degreeCover14_0_3
  · exact degreeCover14_0_4
  · exact degreeCover14_1_0
  · exact degreeCover14_1_1
  · exact degreeCover14_1_2
  · exact degreeCover14_1_3
  · exact degreeCover14_1_4
  · exact degreeCover14_2_0
  · exact degreeCover14_2_1
  · exact degreeCover14_2_2
  · exact degreeCover14_2_3
  · exact degreeCover14_2_4
  · exact degreeCover14_3_0
  · exact degreeCover14_3_1
  · exact degreeCover14_3_2
  · exact degreeCover14_3_3
  · exact degreeCover14_3_4
  · exact degreeCover14_4_0
  · exact degreeCover14_4_1
  · exact degreeCover14_4_2
  · exact degreeCover14_4_3
  · exact degreeCover14_4_4

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeUnionData14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Union Data 14. -/

section

namespace UniversalTensorSquare

lemma degreeHalfHeight14 : ∀ R ∈ degreeHalfRegions14, firstBound 14 R.1 ≤ 13 := by decide +kernel

lemma degreeHalfWidth14 : ∀ R ∈ degreeHalfRegions14, firstBound 14 R.2 ≤ 13 := by decide +kernel

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 14. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch14_0 : checkRegionPrefixes (quickResidual 4 2 degreeQs14 degreeTree14) 0 14 13 degreeHalfRegions14 [] = true := by
  decide +kernel

lemma degreeUnionBranch14_1 : checkRegionPrefixes (quickResidual 4 2 degreeQs14 degreeTree14) 1 14 13 degreeHalfRegions14 [] = true := by
  decide +kernel

lemma degreeUnionBranch14_2 : checkRegionPrefixes (quickResidual 4 2 degreeQs14 degreeTree14) 2 14 13 degreeHalfRegions14 [] = true := by
  decide +kernel

lemma degreeUnionBranch14_3 : checkRegionPrefixes (quickResidual 4 2 degreeQs14 degreeTree14) 3 14 13 degreeHalfRegions14 [] = true := by
  decide +kernel

lemma degreeUnionBranch14_4 : checkRegionPrefixes (quickResidual 4 2 degreeQs14 degreeTree14) 4 14 13 degreeHalfRegions14 [] = true := by
  decide +kernel

lemma degreeUnionBranch14_5 : checkRegionPrefixes (quickResidual 4 2 degreeQs14 degreeTree14) 5 14 13 degreeHalfRegions14 [] = true := by
  decide +kernel

lemma degreeUnionBranch14_6 : checkRegionPrefixes (quickResidual 4 2 degreeQs14 degreeTree14) 6 14 13 degreeHalfRegions14 [] = true := by
  decide +kernel

lemma degreeUnionBranch14_7 : checkRegionPrefixes (quickResidual 4 2 degreeQs14 degreeTree14) 7 14 13 degreeHalfRegions14 [] = true := by
  decide +kernel

lemma degreeUnionBranch14_8 : checkRegionPrefixes (quickResidual 4 2 degreeQs14 degreeTree14) 8 14 13 degreeHalfRegions14 [] = true := by
  decide +kernel

lemma degreeUnionBranch14_9 : checkRegionPrefixes (quickResidual 4 2 degreeQs14 degreeTree14) 9 14 13 degreeHalfRegions14 [] = true := by
  decide +kernel

lemma degreeUnionBranch14_10 : checkRegionPrefixes (quickResidual 4 2 degreeQs14 degreeTree14) 10 14 13 degreeHalfRegions14 [] = true := by
  decide +kernel

lemma degreeUnionBranch14_11 : checkRegionPrefixes (quickResidual 4 2 degreeQs14 degreeTree14) 11 14 13 degreeHalfRegions14 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch14_12 : checkRegionPrefixes (quickResidual 4 2 degreeQs14 degreeTree14) 12 14 13 degreeHalfRegions14 [] = true := by
  decide +kernel

lemma degreeUnionBranch14_13 : checkRegionPrefixes (quickResidual 4 2 degreeQs14 degreeTree14) 13 14 13 degreeHalfRegions14 [] = true := by
  decide +kernel

end UniversalTensorSquare
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

lemma treeResidual_transpose {M r : ℕ} {qs : List (List ℕ)} {t : RowTree}
    {μ : YoungDiagram} (h : TreeResidual M r qs t μ.transpose.rowLens) :
    TreeResidual M r qs t μ.rowLens := by
  rcases h with h | h | h
  · rcases h with h | h | ⟨q,hq,h | h⟩ | h | h
    · exact Or.inl (Or.inr (Or.inl (by simpa only [transposeRows_rowLens] using h)))
    · exact Or.inl (Or.inl (by simpa only [transposeRows_rowLens,
        YoungDiagram.transpose_transpose] using h))
    · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨q,hq,Or.inr (by
        simpa only [transposeRows_rowLens] using h)⟩)))
    · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨q,hq,Or.inl (by
        simpa only [transposeRows_rowLens,YoungDiagram.transpose_transpose] using h)⟩)))
    · simp at h
    · simp at h
  · exact Or.inr (Or.inr (by simpa only [transposeRows_rowLens] using h))
  · exact Or.inr (Or.inl (by simpa only [transposeRows_rowLens,
      YoungDiagram.transpose_transpose] using h))

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
-- module Solutions.OAIQ259_US.UniversalSquare_Support_CheckedUnionSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Checked Union Symmetry. -/

section

namespace UniversalTensorSquare

lemma checkedUnion_symmetric {n M r H W : ℕ} {qs : List (List ℕ)} {t : RowTree}
    {regions allRegions : List PrefixRegion}
    (check : ∀ h ≤ H, checkRegionPrefixes (quickResidual M r qs t) h n W regions [] = true)
    (height : ∀ R ∈ regions, firstBound n R.1 ≤ H)
    (width : ∀ R ∈ regions, firstBound n R.2 ≤ W)
    (cover : ∀ R ∈ allRegions, R ∈ regions ∨ (R.2,R.1) ∈ regions) :
    ∀ R ∈ allRegions, ∀ μ : YoungDiagram, μ.card = n →
      RowBounds μ.transpose R.1 → RowBounds μ R.2 → TreeResidual M r qs t μ.rowLens := by
  intro R hR μ hμ hA hB
  rcases cover R hR with h | h
  · exact checkedRegion_diagram check μ hμ h hA hB (height R h) (width R h)
  · apply treeResidual_transpose
    apply checkedRegion_diagram check μ.transpose ((Saxl.transpose_card μ).trans hμ) h
    · simpa only [YoungDiagram.transpose_transpose] using hB
    · exact hA
    · exact height _ h
    · exact width _ h

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 14. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck14 : ∀ h ≤ 13,
    checkRegionPrefixes (quickResidual 4 2 degreeQs14 degreeTree14) h 14 13 degreeHalfRegions14 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch14_0
  · exact degreeUnionBranch14_1
  · exact degreeUnionBranch14_2
  · exact degreeUnionBranch14_3
  · exact degreeUnionBranch14_4
  · exact degreeUnionBranch14_5
  · exact degreeUnionBranch14_6
  · exact degreeUnionBranch14_7
  · exact degreeUnionBranch14_8
  · exact degreeUnionBranch14_9
  · exact degreeUnionBranch14_10
  · exact degreeUnionBranch14_11
  · exact degreeUnionBranch14_12
  · exact degreeUnionBranch14_13

lemma degreeHalfCover14 : ∀ R ∈ degreeRegions14,
    R ∈ degreeHalfRegions14 ∨ (R.2,R.1) ∈ degreeHalfRegions14 := by decide +kernel

lemma degreeDiagramRegionsChecked14 : ∀ R ∈ degreeRegions14,
    ∀ μ : YoungDiagram, μ.card = 14 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP14 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck14 degreeHalfHeight14 degreeHalfWidth14
    degreeHalfCover14

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeChecks14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Checks 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck14_oai : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      semanticResidualCheck 14 4 2 (d+1) (e+1) (a+1) (c+1) degreeRows14_0 degreeP14 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked14 (degreeCover14 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCheck14_oai := @OAI.UniversalTensorSquare.degreeCheck14_oai
