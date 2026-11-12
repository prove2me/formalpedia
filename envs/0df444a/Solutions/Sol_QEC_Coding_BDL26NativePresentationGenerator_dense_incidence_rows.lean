-- Prove2me | solution 1 for QEC.Coding.BDL26NativePresentationGenerator.dense_incidence_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:04:13.945914+00:00
-- url     : https://prove2.me/submissions/792c926a-9edb-4c90-a48a-af79ad4a2906

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_xq_correct
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_qz_correct
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativePresentationGenerator
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement hiding Two
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26RandomPerturbation
namespace QEC.Coding.BDL26NativePresentationGenerator
theorem _root_.solution (S : OddScale) (n : ℕ)
    (x : (state S n).presentation.X) (q : (state S n).presentation.Q)
    (z : (state S n).presentation.Z) :
    (((generatedRefines S n).xIndex x).val,((generatedRefines S n).qIndex q).val,
      (state S n).presentation.xq x q)∈(runQ S n).1.xq ∧
    (((generatedRefines S n).qIndex q).val,((generatedRefines S n).zIndex z).val,
      (state S n).presentation.qz q z)∈(runQ S n).1.qz := by
  constructor
  · exact (denseXQQ_mem _ _ _ _).mpr
      ⟨((generatedRefines S n).xIndex x).isLt,
        ((generatedRefines S n).qIndex q).isLt,(xq_correct S n x q).symm⟩
  · exact (denseQZQ_mem _ _ _ _).mpr
      ⟨((generatedRefines S n).qIndex q).isLt,
        ((generatedRefines S n).zIndex z).isLt,(qz_correct S n q z).symm⟩
end QEC.Coding.BDL26NativePresentationGenerator
