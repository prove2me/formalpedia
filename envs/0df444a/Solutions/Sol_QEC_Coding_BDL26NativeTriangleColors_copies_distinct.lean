-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.copies_distinct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:15:25.388424+00:00
-- url     : https://prove2.me/submissions/914529f6-9260-4802-bee0-86754d6971af

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_encode_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26NativeTriangleColors
theorem _root_.solution (S : OddScale) (n : ℕ) (f : (P S n).Face) :
    nativeRow S n (f,0)≠nativeRow S n (f,1) := by
  intro h
  have he := BDL26NativeTriangleKeys.encode_injective S n (congrArg Prod.fst h)
  have hd := congrArg (fun t : Triangle (P S n) => t.2.val) he
  norm_num at hd
end QEC.Coding.BDL26NativeTriangleColors
