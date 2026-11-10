-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPhysicalLocality.qubitCorner_recovers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:44:47.513261+00:00
-- url     : https://prove2.me/submissions/eed19a3e-8e01-47f9-9674-8617159b961d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_faceQ_surjective


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPhysicalLocality
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open BDL26TannerLocalRegularity
open BDL26QuantitativeBounds BDL26DecodingGraph BDL26CSSHamiltonian
open Semantics Semantics.Davies
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26RandomPhysicalLocality
theorem _root_.solution (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) : P.faceQ (qubitCorner P A q).1 (qubitCorner P A q).2 = q :=
  Classical.choose_spec (faceQ_surjective P A q)
end QEC.Coding.BDL26RandomPhysicalLocality
