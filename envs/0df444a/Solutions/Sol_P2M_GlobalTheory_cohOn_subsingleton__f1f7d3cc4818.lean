-- Prove2me | solution 1 for P2M_GlobalTheory_cohOn_subsingleton__f1f7d3cc4818
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:46:08.996708+00:00
-- url     : https://prove2.me/submissions/8a1776d1-1b3c-43d4-be03-34a1fafb8a26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_SheafLES_subsingleton__c7111a18855b


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
namespace GlobalTheory.cohOn
theorem _root_.solution (h₂ : Subsingleton (cohOn S.X₂ U n))
    (h₁ : Subsingleton (cohOn S.X₁ U (n + 1))) : Subsingleton (cohOn S.X₃ U n) :=
  SheafLES.subsingleton₃.{u} (shortExact_toAbSheaf hS) n U h₂ h₁
end GlobalTheory.cohOn
