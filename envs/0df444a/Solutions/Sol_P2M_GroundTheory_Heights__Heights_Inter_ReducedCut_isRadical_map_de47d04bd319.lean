-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ReducedCut_isRadical_map_de47d04bd319
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:47.726264+00:00
-- url     : https://prove2.me/submissions/78e2f4d9-c513-4a3b-abdc-2a5d710b95b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsReducedCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OrdModEqLengthQuotSup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PReducedCutLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open GroundTheory.Heights₂.Heights.Inter.ReducedCut
open IsLocalRing
variable {T : Type} [CommRing T] (I : Ideal T) (x : T) (Q : Ideal T) [Q.IsPrime]
local notation "𝓛" => Localization.AtPrime Q
local notation "ι" => algebraMap T (Localization.AtPrime Q)
local notation "𝓘" => Ideal.map (algebraMap T (Localization.AtPrime Q)) I
local notation "𝓐" => Localization.AtPrime Q ⧸ Ideal.map (algebraMap T (Localization.AtPrime Q)) I
local notation "π" => Ideal.Quotient.mk (Ideal.map (algebraMap T (Localization.AtPrime Q)) I)
namespace GroundTheory.Heights₂.Heights.Inter.ReducedCut
theorem _root_.solution (hI : I.IsRadical) : (𝓘).IsRadical := by
  show (𝓘).radical ≤ _
  rw [← IsLocalization.map_radical Q.primeCompl (Localization.AtPrime Q) I, hI.radical]
end GroundTheory.Heights₂.Heights.Inter.ReducedCut
