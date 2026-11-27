-- Prove2me | solution 1 for P2M_GlobalTheory_CechAcyclicMod_of_shortExact__4c4247d18efb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:05:41.921312+00:00
-- url     : https://prove2.me/submissions/606111d3-e346-46e0-95c2-7ba388b3633a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PresheafCubeExactAtSuccOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsAddEquivOfSurjectiveOfKerIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechModulesFunctorShortExactOfAcyclic
import Theorems.Thm_P2M_GlobalTheory_SheafLES_subsingleton__c7111a18855b
import Theorems.Thm_P2M_GlobalTheory_cohOn_subsingleton__f1f7d3cc4818


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
variable {X : Scheme.{u}} {ι : Type}
variable {V : X.Opens} {U : ι → X.Opens} {F G : X.Modules}
namespace GlobalTheory
namespace CechAcyclicMod
theorem _root_.solution {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : CechAcyclicMod V U S.X₁) (h₂ : CechAcyclicMod V U S.X₂) : CechAcyclicMod V U S.X₃ :=
  fun s hs q => cohOn.subsingleton₃ hS _ _ (h₂ s hs q) (h₁ s hs (q + 1))
end CechAcyclicMod
end GlobalTheory
