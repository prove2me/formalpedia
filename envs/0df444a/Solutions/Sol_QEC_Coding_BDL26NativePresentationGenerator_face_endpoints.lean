-- Prove2me | solution 1 for QEC.Coding.BDL26NativePresentationGenerator.face_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:42:33.05546+00:00
-- url     : https://prove2.me/submissions/28c04af8-b36c-4476-8cff-50fb0a401173

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
theorem _root_.solution (S : OddScale) (n : ℕ) (f : (state S n).presentation.Face) :
    let F := (generateQ S n).1
    let r := generatedRefines S n
    let row := (faceAtQ F.faces (r.fIndex f).val).1
    row.x=(r.xIndex ((state S n).presentation.faceX f)).val ∧
      row.z=(r.zIndex ((state S n).presentation.faceZ f)).val ∧
      row.q0=(r.qIndex ((state S n).presentation.faceQ f 0)).val ∧
      row.q1=(r.qIndex ((state S n).presentation.faceQ f 1)).val := by
  let r := generatedRefines S n
  exact ⟨r.face_x f,r.face_z f,r.face_q0 f,r.face_q1 f⟩
end QEC.Coding.BDL26NativePresentationGenerator
