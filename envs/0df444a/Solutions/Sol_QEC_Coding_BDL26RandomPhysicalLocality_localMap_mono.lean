-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPhysicalLocality.localMap_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:45:18.332787+00:00
-- url     : https://prove2.me/submissions/228d9c80-909d-44d4-bb25-18b08ed3ef72

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
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
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → E)
    {s t : ℝ} (hJ : IsBoundedDensityLocalMap P J s) (hst : s ≤ t) :
    IsBoundedDensityLocalMap P J t :=
  ⟨hJ.1, hJ.2.1, fun c => (hJ.2.2 c).trans hst⟩
end QEC.Coding.BDL26RandomPhysicalLocality
