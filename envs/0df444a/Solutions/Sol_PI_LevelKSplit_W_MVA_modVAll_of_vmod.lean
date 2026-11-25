-- Prove2me | solution 1 for PI.LevelKSplit.W.MVA.modVAll_of_vmod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:38:35.303841+00:00
-- url     : https://prove2.me/submissions/0a30c618-ddb6-48b8-b975-23bb679f0e5e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousFirstOrbitMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_OrthogonalInvarianceOfStableRankOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ModulusAllExtensions
import Theorems.Thm_PI_LevelKSplit_W_MVA_pres_snd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.MVA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
namespace PI.LevelKSplit.W.MVA
theorem _root_.solution (h : PI.VolSemiDirect.W.Cj.VMod) : PI.LevelKSplit.W.CD.ModVAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  intro _ _ g μ hμ
  exact pres_snd (InfiniteAdeleRing F) (Af F) σ J
    (fun g' ν hν => h F E σ hσ M J hJ g' ν hν) g μ hμ
end PI.LevelKSplit.W.MVA
