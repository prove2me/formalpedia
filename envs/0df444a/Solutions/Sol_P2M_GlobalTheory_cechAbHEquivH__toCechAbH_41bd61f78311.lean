-- Prove2me | solution 1 for P2M_GlobalTheory_cechAbHEquivH__toCechAbH_41bd61f78311
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:09:58.149447+00:00
-- url     : https://prove2.me/submissions/d4c49d37-6528-43d5-8255-8707b6cab1b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PresheafCubeExactAtSuccOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsAddEquivOfSurjectiveOfKerIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechModulesFunctorShortExactOfAcyclic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe v u
noncomputable section
open GlobalTheory
variable {T : TopCat.{u}} {ι : Type}
variable {V : Opens T} {U : ι → Opens T}
variable [LinearOrder ι]
variable [Finite ι] (hc : V ≤ ⨆ i, U i)
variable {F G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}}
namespace GlobalTheory
theorem _root_.solution (hF : CechAcyclic V U F) (x : F.obj.obj (op V)) :
    cechAbHEquivH' hc hF 0 (toCechAbH F.obj V U x) = (SheafLES.equivZero F V).symm x :=
  congrArg (SheafLES.equivZero F V).symm
    ((cechAbHZeroEquiv F.property hc).apply_symm_apply x)
end GlobalTheory
