-- Prove2me | solution 1 for P2M_GlobalTheory_cohOn_finite__b0203fc991a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:09:25.457974+00:00
-- url     : https://prove2.me/submissions/80ada29d-292e-4d53-869b-61c69fdbf8b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_GlobalTheory_ExactSeq_finite
import Theorems.Thm_P2M_GlobalTheory_cohOn_exact__c8d68170d18d
import Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__24269ba80ece


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Module
universe t v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
open GlobalTheory.cohOn
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
  {S : ShortComplex X.Modules} (hS : S.ShortExact)
variable (U : X.Opens) (n : ℕ)
include hS
variable [IsNoetherianRing R]
namespace GlobalTheory.cohOn
theorem _root_.solution (h₂ : Module.Finite R (cohOn S.X₂ U n))
    (h₁ : Module.Finite R (cohOn S.X₁ U (n + 1))) : Module.Finite R (cohOn S.X₃ U n) :=
  ExactSeq.finite (exact₃ R hS U n)
end GlobalTheory.cohOn
