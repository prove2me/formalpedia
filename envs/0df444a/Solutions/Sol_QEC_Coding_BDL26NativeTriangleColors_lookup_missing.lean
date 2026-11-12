-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.lookup_missing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:27:08.631412+00:00
-- url     : https://prove2.me/submissions/1b4f8e32-366f-439a-9499-e9a7ea31c9c6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_row_code
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_colors_value
import Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_atlas_read_missing

section
namespace QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
namespace G
export BDL26NativePresentationGenerator (Code)
end G
open G
noncomputable section Semantic
variable (P : TannerSquarePresentation) (key : Triangle P → ℕ)
end Semantic
noncomputable section Actual
open scoped Classical
private theorem colors_pairs (S : OddScale) (n : ℕ) :
    (colorsQ S n).value=(T S n).map (fun c =>
      (c,(colorRowQ (BDL26NativeSupportMetadata.atlasQ S n).value c).value.2)) := by
  rw [colors_value]
  apply List.map_congr_left
  intro c _
  apply Prod.ext
  · exact row_code _ c
  · rfl
end Actual
end QEC.Coding.BDL26NativeTriangleColors
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26NativeTriangleColors
theorem _root_.solution (S : OddScale) (n : ℕ) (c : Code) (hc : c∉T S n) :
    (colorOfCodeQ S n c).value=none := by
  change (BDL26NativeSupportMetadata.atlasReadQ c (colorsQ S n).value).value=none
  rw [colors_pairs]
  exact (BDL26NativeSupportMetadata.atlas_read_missing _ c (T S n) hc).1
end QEC.Coding.BDL26NativeTriangleColors
