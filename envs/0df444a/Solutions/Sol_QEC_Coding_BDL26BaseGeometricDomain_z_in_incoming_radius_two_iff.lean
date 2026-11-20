-- Prove2me | solution 1 for QEC.Coding.BDL26BaseGeometricDomain.z_in_incoming_radius_two_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:51:27.931364+00:00
-- url     : https://prove2.me/submissions/67274fb6-4b96-4fc4-a4a8-098da96c151f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint
import Theorems.Thm_QEC_Coding_BDL26BaseGeometricDomain_tanner_z_in_incoming_iff

set_option autoImplicit false
noncomputable section
noncomputable section
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BaseGeometricDomain
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open scoped Classical
namespace QEC.Coding.BDL26BaseGeometricDomain
theorem _root_.solution (S : OddScale) (n : Nat)
    (z : (state S n).presentation.Z) (v : Vertex (state S n).presentation) :
    Vertex.z z ∈ LocalRegion.directedNeighborhood
      (tannerLevel (state S n).presentation).graph v 2 ↔ Vertex.z z=v := by
  exact tanner_z_in_incoming_iff (state S n).presentation z v 2
end QEC.Coding.BDL26BaseGeometricDomain
