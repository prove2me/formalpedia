-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPhysicalLocality.physicalGeometry_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:45:11.429331+00:00
-- url     : https://prove2.me/submissions/f3223c3d-c97e-4f14-ab3c-88049c8ac2ed

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPhysicalLocality
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open BDL26TannerLocalRegularity
open BDL26QuantitativeBounds BDL26DecodingGraph BDL26CSSHamiltonian
open Semantics Semantics.Davies
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26RandomPhysicalLocality
theorem _root_.solution (S : OddScale) (m n : Nat) (h : m = n)
    (J : Vertex (state S m).presentation → E) (t : ℝ) (hg : PhysicalGeometry S m J t) :
    PhysicalGeometry S n
      (fun v => J (cast (congrArg (fun a => Vertex (state S a).presentation) h.symm) v)) t := by
  subst n
  exact hg
end QEC.Coding.BDL26RandomPhysicalLocality
