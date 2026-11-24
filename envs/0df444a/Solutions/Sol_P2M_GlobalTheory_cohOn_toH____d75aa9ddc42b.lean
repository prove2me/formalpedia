-- Prove2me | solution 1 for P2M_GlobalTheory_cohOn_toH____d75aa9ddc42b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:45:03.975639+00:00
-- url     : https://prove2.me/submissions/37066bac-7509-41c4-9c3c-4f9bb4b9293f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero

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
theorem _root_.solution (x : cohOn S.X₃ U n) :
    toH' S.X₁ U (n + 1) (δ R hS U n x) =
      SheafLES.δ.{u} (shortExact_toAbSheaf hS) n U (toH' S.X₃ U n x) := rfl
end GlobalTheory.cohOn
