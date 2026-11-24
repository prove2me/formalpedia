-- Prove2me | solution 1 for P2M_GlobalTheory_cohOn___map_6ba3242e7e5e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:00:05.43786+00:00
-- url     : https://prove2.me/submissions/d9214b76-ac42-42e2-bc2c-6df66217a7d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
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
namespace GlobalTheory.cohOn
theorem _root_.solution (x : cohOn S.X₂ U n) : δ R hS U n (map R S.g U n x) = 0 :=
  (exact₃ R hS U n).apply_apply_eq_zero x
end GlobalTheory.cohOn
