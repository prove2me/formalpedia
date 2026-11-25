-- Prove2me | solution 1 for PI.SymDistWork.inUJ_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:28:58.706131+00:00
-- url     : https://prove2.me/submissions/d2560208-2b11-4bde-a86f-7d79cf35e3b1

import Definitions.Def_Formalism_PeriodIntegrals_SymDist
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SymmetricDistance_SymDistOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.SymDistWork
open Formalism.REAL
variable {n : ℕ}
namespace PI.SymDistWork
theorem _root_.solution {ε : Fin n → Bool} (g : UJ ε) :
    inUJ ε ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
  exact g.2
end PI.SymDistWork
