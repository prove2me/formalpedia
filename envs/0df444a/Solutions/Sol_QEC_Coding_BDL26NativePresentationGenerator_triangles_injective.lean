-- Prove2me | solution 1 for QEC.Coding.BDL26NativePresentationGenerator.triangles_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:47:51.004798+00:00
-- url     : https://prove2.me/submissions/cf6e735b-e510-4fbe-a445-929f1304e62e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativePresentationGenerator
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement hiding Two
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26RandomPerturbation
namespace QEC.Coding.BDL26NativePresentationGenerator
theorem _root_.solution (S : OddScale) (n : ℕ) :
    Function.Injective (fun a : (state S n).presentation.Face × Two =>
      ({family:=3,owner:=((generatedRefines S n).fIndex a.1).val,copy:=a.2.val} : Code)) := by
  intro a b h
  have hf := congrArg Code.owner h
  have hd := congrArg Code.copy h
  exact Prod.ext ((index_val_eq (generatedRefines S n).fIndex _ _).mp hf) (Fin.ext hd)
end QEC.Coding.BDL26NativePresentationGenerator
