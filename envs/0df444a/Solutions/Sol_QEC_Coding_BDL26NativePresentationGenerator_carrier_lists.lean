-- Prove2me | solution 1 for QEC.Coding.BDL26NativePresentationGenerator.carrier_lists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:00:28.381193+00:00
-- url     : https://prove2.me/submissions/fad9d48e-3dc4-4f83-96b0-388469be5aaf

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
    let F := (generateQ S n).1
    F.xs.length=F.nx ∧ F.qs.length=F.nq ∧ F.zs.length=F.nz ∧ F.faces.length=F.nf ∧
      F.xs.Nodup ∧ F.qs.Nodup ∧ F.zs.Nodup ∧ (F.faces.map FaceRow.code).Nodup := by
  let r := generatedRefines S n
  exact ⟨r.x_length,r.q_length,r.z_length,r.f_length,r.x_nodup,r.q_nodup,r.z_nodup,r.f_nodup⟩
end QEC.Coding.BDL26NativePresentationGenerator
