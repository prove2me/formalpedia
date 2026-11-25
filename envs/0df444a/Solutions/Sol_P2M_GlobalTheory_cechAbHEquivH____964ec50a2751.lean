-- Prove2me | solution 1 for P2M_GlobalTheory_cechAbHEquivH____964ec50a2751
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:09:55.773402+00:00
-- url     : https://prove2.me/submissions/ed40275a-4b7e-4457-8eb0-8eb292bf3f5d

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
theorem _root_.solution
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})} (hS : S.ShortExact)
    (h₁ : CechAcyclic V U S.X₁) (h₃ : CechAcyclic V U S.X₃) (n : ℕ) (x : cechAbH S.X₃.obj V U n) :
    cechAbHEquivH' hc h₁ (n + 1) (cechAbδ hS h₁ n x) =
      SheafLES.δ hS n V (cechAbHEquivH' hc h₃ n x) :=
  (cechComparisonOfCover hc n).exists_succ.choose_spec S hS h₁ h₃ x
end GlobalTheory
