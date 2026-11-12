-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.output_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:14:06.23323+00:00
-- url     : https://prove2.me/submissions/6bb1db59-a7a1-427c-ab4d-43fe681b1fc6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_native_rank_lt
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_output_unique
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26NativeTriangleColors
theorem _root_.solution (S : OddScale) (n : ℕ)
    (r : ColorRow (BDL26NativeStateRows.Index S n)) (hr : r∈(colorsQ S n).value) :
    ∃t : Triangle (P S n),r=nativeRow S n t ∧
      ∀i : Fin 3,nativeColor S n t i<56 := by
  obtain ⟨t,ht,_⟩ := output_unique S n r hr
  exact ⟨t,ht.symm,native_rank_lt S n t⟩
end QEC.Coding.BDL26NativeTriangleColors
