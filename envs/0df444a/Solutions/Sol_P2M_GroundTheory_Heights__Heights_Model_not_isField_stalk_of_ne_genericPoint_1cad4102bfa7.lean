-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_not_isField_stalk_of_ne_genericPoint_1cad4102bfa7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:05:51.480375+00:00
-- url     : https://prove2.me/submissions/072affd3-64ac-4e0d-8029-63d604f55df0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PDominatingDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PKrullAkizuki
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PKrullAkizukiQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PTorsionFreeQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PBlowUpChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PDominatingDVRScheme

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open AlgebraicGeometry
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (Z : Scheme.{0}) [IsIntegral Z] (z : Z)
    (hz : z ≠ genericPoint Z) : ¬ IsField (Z.presheaf.stalk z) := by
  intro hF
  have hgen : genericPoint Z ⤳ z := (genericPoint_spec Z).specializes trivial
  have hmem : genericPoint Z ∈ Set.range (Z.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]; exact hgen
  obtain ⟨y, hy⟩ := hmem
  have hmax : IsLocalRing.maximalIdeal (Z.presheaf.stalk z) = ⊥ :=
    (IsLocalRing.isField_iff_maximalIdeal_eq.mp hF)
  have hyc : y = IsLocalRing.closedPoint (Z.presheaf.stalk z) := by
    apply PrimeSpectrum.ext
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal y.isPrime.ne_top
    · exact hmax.le.trans bot_le
  apply hz
  rw [← hy, hyc, Scheme.fromSpecStalk_closedPoint]
end GroundTheory.Heights₂.Heights.Model
