-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DivisorBranches_not_mem_zeroSet_of_le_070b3c6613ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:28.212422+00:00
-- url     : https://prove2.me/submissions/73fb64fd-eea8-4483-89ef-15bf78e9b9a1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorBranches
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorRegularGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalDivisorChartGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalDoublePointsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPointBranches
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDivisorBranches

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.DivisorBranches
namespace GroundTheory.Heights₂.Heights.DivisorBranches
theorem _root_.solution {n : ℕ} {I I' : Ideal (MvPolynomial (Fin n) ℂ)} (hle : I ≤ I')
    {q : Fin n → ℂ} (hq : q ∉ zeroSet I) : q ∉ zeroSet I' :=
  fun h => hq fun f hf => h f (hle hf)
end GroundTheory.Heights₂.Heights.DivisorBranches
