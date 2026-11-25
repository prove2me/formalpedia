-- Prove2me | solution 1 for P2M_GlobalTheory_cohOn_forall_finite__b9548819e78a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:34:00.898616+00:00
-- url     : https://prove2.me/submissions/829a6488-c8e4-4151-921c-9a8f9753558e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_cohOn_finite__b0203fc991a1

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
    (h₂ : ∀ n, Module.Finite R (cohOn S.X₂ U n)) : ∀ n, Module.Finite R (cohOn S.X₃ U n) :=
  fun n ↦ finite₃ R hS U n (h₂ n) (h₁ (n + 1))
end GlobalTheory.cohOn
