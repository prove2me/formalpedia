-- Prove2me | solution 1 for P2M_GlobalTheory_cohOn_forall_finite__c3d9f8ce7a16
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:34:04.530487+00:00
-- url     : https://prove2.me/submissions/2bd31f88-b7f4-48c1-8a2c-ccaa596e8ec1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_cohOn_finite__ff84c2925af6
import Theorems.Thm_P2M_GlobalTheory_cohOn_finite__zero_149652da37c5

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
theorem _root_.solution (h₂ : ∀ n, Module.Finite R (cohOn S.X₂ U n))
    (h₃ : ∀ n, Module.Finite R (cohOn S.X₃ U n)) : ∀ n, Module.Finite R (cohOn S.X₁ U n)
  | 0 => finite₁_zero R hS U (h₂ 0)
  | n + 1 => finite₁ R hS U n (h₃ n) (h₂ (n + 1))
end GlobalTheory.cohOn
