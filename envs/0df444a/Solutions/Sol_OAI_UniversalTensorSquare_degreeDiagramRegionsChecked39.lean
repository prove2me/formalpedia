-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeDiagramRegionsChecked39
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:41:08.350296+00:00
-- url     : https://prove2.me/submissions/4d3ff662-3ef3-4f38-b8ce-41955049eb2d

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkedRegion_diagram
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_121
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_2
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_225
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_308
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_309
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_310
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_311
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_312
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_313
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_314
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_315
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_316
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_8
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq

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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeUnionData39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Union Data 39. -/

section

namespace UniversalTensorSquare

lemma degreeHalfHeight39 : ∀ R ∈ degreeHalfRegions39, firstBound 39 R.1 ≤ 19 := by decide +kernel

lemma degreeHalfWidth39 : ∀ R ∈ degreeHalfRegions39, firstBound 39 R.2 ≤ 38 := by decide +kernel

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 39. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_3 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 3 39 38 degreeHalfRegions39 [] = true := by
  decide +kernel

lemma degreeUnionBranch39_4 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 4 39 38 degreeHalfRegions39 [] = true := by
  decide +kernel

lemma degreeUnionBranch39_5 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 5 39 38 degreeHalfRegions39 [] = true := by
  decide +kernel

lemma degreeUnionBranch39_6 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 39 38 degreeHalfRegions39 [] = true := by
  decide +kernel

lemma degreeUnionBranch39_7 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 39 38 degreeHalfRegions39 [] = true := by
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 39. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck39 : ∀ h ≤ 19,
    checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) h 39 38 degreeHalfRegions39 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch39_0
  · exact degreeUnionBranch39_1
  · exact degreeUnionBranch39_2
  · exact degreeUnionBranch39_3
  · exact degreeUnionBranch39_4
  · exact degreeUnionBranch39_5
  · exact degreeUnionBranch39_6
  · exact degreeUnionBranch39_7
  · exact degreeUnionBranch39_8
  · exact degreeUnionBranch39_121
  · exact degreeUnionBranch39_225
  · exact degreeUnionBranch39_308
  · exact degreeUnionBranch39_309
  · exact degreeUnionBranch39_310
  · exact degreeUnionBranch39_311
  · exact degreeUnionBranch39_312
  · exact degreeUnionBranch39_313
  · exact degreeUnionBranch39_314
  · exact degreeUnionBranch39_315
  · exact degreeUnionBranch39_316

lemma degreeHalfCover39 : ∀ R ∈ degreeRegions39,
    R ∈ degreeHalfRegions39 ∨ (R.2,R.1) ∈ degreeHalfRegions39 := by decide +kernel

lemma degreeDiagramRegionsChecked39_oai : ∀ R ∈ degreeRegions39,
    ∀ μ : YoungDiagram, μ.card = 39 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP39 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck39 degreeHalfHeight39 degreeHalfWidth39
    degreeHalfCover39

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeDiagramRegionsChecked39_oai := @OAI.UniversalTensorSquare.degreeDiagramRegionsChecked39_oai
