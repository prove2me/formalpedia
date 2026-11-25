-- Prove2me | solution 1 for PI.DvRows.partB_of_pieces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:47:40.023349+00:00
-- url     : https://prove2.me/submissions/66a16c81-a1d4-4520-95dd-de9e65ceef03

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_AsmBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_AsmDual
import Theorems.Thm_PI_DvRows_degDual_of
import Theorems.Thm_PI_DvRows_degDualBound_of
import Theorems.Thm_PI_DvRows_partB_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.LFunctionChainParameters.LLcv
namespace PI.DvRows
theorem _root_.solution (hFG : LamFG) (hAd : Adapted) (hCS : GramCS) (hAI : ArchIdentity)
    (hLG : LocalGamma) (hLP : LocalPairing) (hCP : ConjPrime) (hNF : NormFinsum) : PartB :=
  partB_of (degDual_of hFG hAd hAI hLP hCP hNF) (degDualBound_of hFG hCS hLG hCP hNF)
end PI.DvRows
