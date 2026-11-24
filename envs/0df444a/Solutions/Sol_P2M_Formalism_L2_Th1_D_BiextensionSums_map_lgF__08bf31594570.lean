-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_D_BiextensionSums_map_lgF__08bf31594570
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:04:08.83707+00:00
-- url     : https://prove2.me/submissions/b95a04e8-d6c7-42ff-b960-5c28e064e9ab

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionPointsOfExpSpec
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionOfExpSpec
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_mvExp_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog thetaZ bSum linSub idM ZV)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog mvExp_add)
open MvPowerSeries
open Pair
open Formalism.L2.Th1.D.BiextensionSums
namespace Formalism.L2.Th1.D.BiextensionSums
theorem _root_.solution {K0 K : Type} [Field K0] [Field K] (l : ℕ) (j : K0 →+* K) :
    PowerSeries.map j (lgF K0 l) = lgF K l := by
  ext n
  rw [PowerSeries.coeff_map]
  unfold lgF
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rw [map_inv₀, map_pow, map_natCast]
  · rw [map_zero]
end Formalism.L2.Th1.D.BiextensionSums
