-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.copy_x_rank_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:11:06.813208+00:00
-- url     : https://prove2.me/submissions/5b9265da-5c6c-4e21-8981-a7e56de51c04

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fiberRank_strictMono


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26NativeTriangleColors
theorem _root_.solution (S : OddScale) (n : ℕ) (f : (P S n).Face) :
    nativeColor S n (f,0) 0<nativeColor S n (f,1) 0 := by
  change fiberRank (nativeKey S n) (fun t : Triangle (P S n) => (P S n).faceX t.1) (f,0)<
    fiberRank (nativeKey S n) (fun t : Triangle (P S n) => (P S n).faceX t.1) (f,1)
  apply fiberRank_strictMono (nativeKey S n)
    (fun t : Triangle (P S n) => (P S n).faceX t.1) (f,0) (f,1) rfl
  change 2*((BDL26NativePresentationGenerator.generatedRefines S n).fIndex f).val+0<
    2*((BDL26NativePresentationGenerator.generatedRefines S n).fIndex f).val+1
  omega
end QEC.Coding.BDL26NativeTriangleColors
