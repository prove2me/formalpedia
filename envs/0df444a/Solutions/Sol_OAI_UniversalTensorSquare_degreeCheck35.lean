-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCheck35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:37:20.70396+00:00
-- url     : https://prove2.me/submissions/f3a0a49b-9f91-416b-a417-9ab4fa7db4d7

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkedRegion_diagram
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionCheck35
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeCover35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Cover 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover35_0_0 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 1 1 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_0_1 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 1 2 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_0_2 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 1 3 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_0_3 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 1 4 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_0_4 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 1 5 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_1_0 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 2 1 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_1_1 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 2 2 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_1_2 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 2 3 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_1_3 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 2 4 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_1_4 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 2 5 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_2_0 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 3 1 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_2_1 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 3 2 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_2_2 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 3 3 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_2_3 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 3 4 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_2_4 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 3 5 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_3_0 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 4 1 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_3_1 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 4 2 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_3_2 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 4 3 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_3_3 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 4 4 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_3_4 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 4 5 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_4_0 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 5 1 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_4_1 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 5 2 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_4_2 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 5 3 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_4_3 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 5 4 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_4_4 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 5 5 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 (d+1) (e+1) (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCover35_0_0
  · exact degreeCover35_0_1
  · exact degreeCover35_0_2
  · exact degreeCover35_0_3
  · exact degreeCover35_0_4
  · exact degreeCover35_1_0
  · exact degreeCover35_1_1
  · exact degreeCover35_1_2
  · exact degreeCover35_1_3
  · exact degreeCover35_1_4
  · exact degreeCover35_2_0
  · exact degreeCover35_2_1
  · exact degreeCover35_2_2
  · exact degreeCover35_2_3
  · exact degreeCover35_2_4
  · exact degreeCover35_3_0
  · exact degreeCover35_3_1
  · exact degreeCover35_3_2
  · exact degreeCover35_3_3
  · exact degreeCover35_3_4
  · exact degreeCover35_4_0
  · exact degreeCover35_4_1
  · exact degreeCover35_4_2
  · exact degreeCover35_4_3
  · exact degreeCover35_4_4

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeUnionData35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Union Data 35. -/

section

namespace UniversalTensorSquare

lemma degreeHalfHeight35 : ∀ R ∈ degreeHalfRegions35, firstBound 35 R.1 ≤ 15 := by decide +kernel

lemma degreeHalfWidth35 : ∀ R ∈ degreeHalfRegions35, firstBound 35 R.2 ≤ 34 := by decide +kernel

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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 35. -/

section

namespace UniversalTensorSquare

lemma degreeHalfCover35 : ∀ R ∈ degreeRegions35,
    R ∈ degreeHalfRegions35 ∨ (R.2,R.1) ∈ degreeHalfRegions35 := by decide +kernel

lemma degreeDiagramRegionsChecked35 : ∀ R ∈ degreeRegions35,
    ∀ μ : YoungDiagram, μ.card = 35 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP35 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck35 degreeHalfHeight35 degreeHalfWidth35
    degreeHalfCover35

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeChecks35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Checks 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck35_oai : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      semanticResidualCheck 35 6 7 (d+1) (e+1) (a+1) (c+1) degreeRows35_0 degreeP35 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked35 (degreeCover35 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCheck35_oai := @OAI.UniversalTensorSquare.degreeCheck35_oai
