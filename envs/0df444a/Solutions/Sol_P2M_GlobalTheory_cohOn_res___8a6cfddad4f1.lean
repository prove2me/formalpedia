-- Prove2me | solution 1 for P2M_GlobalTheory_cohOn_res___8a6cfddad4f1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:52:40.791826+00:00
-- url     : https://prove2.me/submissions/7aaed96b-0f3c-4ec4-b3d3-80a9c871ab83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_SheafLES___res_2b8f5cf68032


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
variable {U}
namespace GlobalTheory.cohOn
theorem _root_.solution {V : X.Opens} (h : V ≤ U) (x : cohOn S.X₃ U n) :
    res R S.X₁ h (n + 1) (δ R hS U n x) = δ R hS V n (res R S.X₃ h n x) :=
  SheafLES.δ_res.{u} (shortExact_toAbSheaf hS) n (homOfLE h) x
end GlobalTheory.cohOn
