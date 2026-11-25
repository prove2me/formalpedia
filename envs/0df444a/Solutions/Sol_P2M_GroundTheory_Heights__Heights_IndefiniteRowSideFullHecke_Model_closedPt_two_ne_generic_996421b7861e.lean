-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_closedPt_two_ne_generic_996421b7861e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:33:21.616793+00:00
-- url     : https://prove2.me/submissions/99c1006d-22f9-41b0-bc43-a41203a4301c

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_WeilDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory Opposite AlgebraicGeometry Limits TopologicalSpace MonoidalCategory
open GroundTheory.Arith.SchemeCoh
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
theorem _root_.solution : closedPt prime2 ≠ genericPoint specInt := by
  intro h
  have hs : genericPoint specInt ⤳ closedPt prime3 := genericPoint_specializes _
  rw [← h] at hs
  have hle : primePt prime2 ≤ primePt prime3 :=
    (PrimeSpectrum.le_iff_specializes (primePt prime2) (primePt prime3)).mpr hs
  have h2 : ((2 : ℕ) : ℤ) ∈ Ideal.span {((3 : ℕ) : ℤ)} :=
    ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hle) (Ideal.subset_span rfl)
  rw [Ideal.mem_span_singleton] at h2
  norm_num at h2
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
