-- Prove2me | solution 1 for P2M_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_Model_div__0f88e1ce6105
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:51:42.23446+00:00
-- url     : https://prove2.me/submissions/6205a539-ed1d-4d59-9d44-ccb85184b796

import Definitions.Def_Formalism_SizeWindowBrackets_SlopeHypothesesRounded
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedSlopeExcessDecomposition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices
import Theorems.Thm_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_Model_sum_abs_ge
import Theorems.Thm_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_Model_LaV_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LatticeToWeightTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
open Formalism.LFunctionChainParameters.LatticeToWeightTransfer.Model
namespace Formalism.LFunctionChainParameters.LatticeToWeightTransfer.Model
theorem _root_.solution (μ0 μ1 μ2 : ℝ) (h : Fin 20 → ℝ) : (D1 μ0 μ1 μ2 h).DIV C2 := by
  intro u0 u
  have h1 := le_abs_self μ0
  have h2 := (le_abs_self (h u)).trans (sum_abs_ge h u)
  have h3 := neg_abs_le FoV
  have h4 := LaV_nonneg μ0 μ1 h
  have h5 := abs_nonneg EeV
  simp [D1, C2, Data.nT, Data.logOm, ph, Real.pi_ne_zero, NcV]
  linarith
end Formalism.LFunctionChainParameters.LatticeToWeightTransfer.Model
