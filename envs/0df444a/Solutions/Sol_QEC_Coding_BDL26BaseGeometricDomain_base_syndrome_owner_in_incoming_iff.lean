-- Prove2me | solution 1 for QEC.Coding.BDL26BaseGeometricDomain.base_syndrome_owner_in_incoming_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:51:24.48098+00:00
-- url     : https://prove2.me/submissions/3eed740f-d271-4266-8179-62d21b521144

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
    (p : BDL26IndexedDecoder.FamilyZ S (n+2)
      (LevelTwoHistory.physicalLevel (0 : LevelIndex n)))
    (center : GraphVertex S 2) (radius : Nat) :
    BDL26CanonicalHistoryMarks.baseSyndromeOwner S n p ∈
      LocalRegion.directedNeighborhood (level S 2).graph center radius ↔
        BDL26CanonicalHistoryMarks.baseSyndromeOwner S n p=center := by
  change Vertex.z (BDL26ReplacementSupport.rzSyndromeOwner
      (state S 1).presentation S p) ∈ LocalRegion.directedNeighborhood
      (tannerLevel (state S 1).presentation).graph center radius ↔
    Vertex.z (BDL26ReplacementSupport.rzSyndromeOwner
      (state S 1).presentation S p)=center
  exact tanner_z_in_incoming_iff (state S 1).presentation _ center radius
end QEC.Coding.BDL26BaseGeometricDomain
