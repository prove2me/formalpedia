-- Prove2me | solution 1 for QEC.Coding.BDL26NativePresentationGenerator.native_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:00:35.933206+00:00
-- url     : https://prove2.me/submissions/599a59a1-5c9c-41a0-9386-976bba912a0e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_xqIncidenceMatrix_mul_qzIncidenceMatrix


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativePresentationGenerator
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement hiding Two
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26RandomPerturbation
namespace QEC.Coding.BDL26NativePresentationGenerator
theorem _root_.solution (S : OddScale) (n : ℕ) :
    nativeXQ (generateQ S n).1 * nativeQZ (generateQ S n).1=0 := by
  classical
  let P := (state S n).presentation
  let r := generatedRefines S n
  ext x z
  obtain ⟨a,rfl⟩ := r.xIndex.surjective x
  obtain ⟨b,rfl⟩ := r.zIndex.surjective z
  rw [Matrix.mul_apply]
  have hreindex := Fintype.sum_equiv r.qIndex
    (fun q : P.Q => (xqIncidenceMatrix P a q)*(qzIncidenceMatrix P q b))
    (fun q : Fin (generateQ S n).1.nq =>
      nativeXQ (generateQ S n).1 (r.xIndex a) q *
        nativeQZ (generateQ S n).1 q (r.zIndex b)) (by
      intro q
      change (if P.xq a q then (1:BDL26FiniteTannerSquare.Field) else 0)*
          (if P.qz q b then 1 else 0)=
        (if (xqQ (generateQ S n).1 (r.xIndex a).val (r.qIndex q).val).1 then 1 else 0)*
          (if (qzQ (generateQ S n).1 (r.qIndex q).val (r.zIndex b).val).1 then 1 else 0)
      rw [refines_xq r (state S n).admissible.toTannerSquareAdmissible,
        refines_qz r (state S n).admissible.toTannerSquareAdmissible])
  rw [←hreindex]
  exact congrFun (congrFun (xqIncidenceMatrix_mul_qzIncidenceMatrix P) a) b
end QEC.Coding.BDL26NativePresentationGenerator
