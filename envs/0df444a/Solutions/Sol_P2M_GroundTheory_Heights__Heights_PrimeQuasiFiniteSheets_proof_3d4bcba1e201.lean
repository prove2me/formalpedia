-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_proof_3d4bcba1e201
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:08:24.841142+00:00
-- url     : https://prove2.me/submissions/3775f5fa-80bb-4a9f-9f2f-911948ea1964

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimeQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFiniteFibresDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StDominantPrimitiveFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSimpleRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPrimeQuasiFiniteSheets
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_sheets_of_not_injective_d59186b2379e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_sheets_of_parametrisation_e159ba74b0c7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace PrimeQuasiFiniteSheets
theorem _root_.solution (hFF : FiniteFibresDimLe.Statement)
    (hDP : DominantPrimitiveFibres.Statement) (hSR : ComplexSets.SimpleRootBranch.Statement) :
    PrimeQuasiFiniteSheets.Statement := by
  intro n d Q A hQ hfin
  by_cases hinj : Function.Injective (ComplexSets.projHom Q A)
  · obtain ⟨c, m, Δ, S, hΔ, hP⟩ := hDP n d Q A hQ (hFF n d Q A hQ hfin) hinj
    exact ⟨Δ, hΔ, PrimeQuasiFiniteSheets.sheets_of_parametrisation hSR c m Δ S hP⟩
  · exact PrimeQuasiFiniteSheets.sheets_of_not_injective Q A hinj
end PrimeQuasiFiniteSheets
end GroundTheory.Heights₂.Heights
