-- Prove2me | solution 1 for P2M_GlobalTheory_cohOn_forall_finite__9ed7f3adb97b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:33:56.770145+00:00
-- url     : https://prove2.me/submissions/916f2be9-ee70-4db5-ba76-8ca015680ed6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_cohOn_finite__b94ea04ef99c

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
theorem _root_.solution (h₁ : ∀ n, Module.Finite R (cohOn S.X₁ U n))
    (h₃ : ∀ n, Module.Finite R (cohOn S.X₃ U n)) : ∀ n, Module.Finite R (cohOn S.X₂ U n) :=
  fun n ↦ finite₂ R hS U n (h₁ n) (h₃ n)
end GlobalTheory.cohOn
