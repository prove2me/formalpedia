-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPhysicalLocality.qubit_density_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:54:14.80961+00:00
-- url     : https://prove2.me/submissions/a6bab1e6-1f96-42bb-9332-a2bad4092043

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_qubitHits_card_le
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
    (J : Vertex P → E) {t : ℝ} (hJ : IsBoundedDensityLocalMap P J t) (c : E) :
    ((qubitHits P J (Metric.closedBall c 1)).card : ℝ) ≤ 2*t := by
  have hc : ((qubitHits P J (Metric.closedBall c 1)).card : ℝ) ≤
      2*((familyHits (tannerFaceImage P J) (Metric.closedBall c 1)).card : ℝ) := by
    exact_mod_cast qubitHits_card_le P A J (Metric.closedBall c 1)
  exact hc.trans (mul_le_mul_of_nonneg_left (hJ.2.2 c) (by norm_num))
end QEC.Coding.BDL26RandomPhysicalLocality
