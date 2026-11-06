-- Prove2me | solution 1 for QEC.Locality.fixedGeneratorOuterBoundary_interior_card_le_sharedBoundary_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:13:25.057795+00:00
-- url     : https://prove2.me/submissions/d5cc7411-1afe-4c28-813b-84fd059838ce

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Theorems.Thm_QEC_Locality_fixedGeneratorOuterBoundary_interior_subset_sharedBoundary

set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    {κ : Type v} [Fintype κ] {m : Type w} [DecidableEq m]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    {regions : m → Finset (ι × ι)} {active : Finset m}
    (hDivision : IsEdgeDivision P.fixedGeneratorInteractionGraph regions active)
    {i : m} (hi : i ∈ active) :
    (fixedGeneratorOuterBoundaryFinset P
      (edgeDivisionInterior regions active i)).card ≤
        (edgeDivisionSharedBoundary regions active).card :=
  Finset.card_le_card
    (fixedGeneratorOuterBoundary_interior_subset_sharedBoundary P hDivision hi)
end QEC.Locality
