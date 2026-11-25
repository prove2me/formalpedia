-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_D_CohomologyFunctoriality__norm_iter_c6ab79c48f38
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:34:10.759864+00:00
-- url     : https://prove2.me/submissions/f758b2f3-c923-454a-94f5-c05c1955308b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_ThetaInZIsThetaLog
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_GaussJetBounds_ThmAEntryFull
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGauss
import Definitions.Def_Formalism_GaussJetBounds_ThmAGauss
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThetaLogIsSubst
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ThetaIntegerIsSSubstitution
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_L2_Th1_D_frobSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp Unram entLog oneLog thetaZ thetaOne frameJet frameJetOne
  nablaO)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp OmOK lamF thetaLog sSub zLin)
open Formalism.L2.Th1.D.CohomologyFunctoriality₂
namespace Formalism.L2.Th1.D.CohomologyFunctoriality₂
theorem _root_.solution {K0 : Type} [NormedField K0] [IsUltrametricDist K0] [CharZero K0] {l : ℕ}
    {σ : K0 →+* K0} (hU : UnrOK K0 l σ) {c : K0} (hc : ‖c‖ ≤ 1) (n : ℕ) : ‖σ^[n] c‖ ≤ 1 := by
  induction n with
  | zero => simpa using hc
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (frobSq K0 l σ hU).2 _ ih
end Formalism.L2.Th1.D.CohomologyFunctoriality₂
