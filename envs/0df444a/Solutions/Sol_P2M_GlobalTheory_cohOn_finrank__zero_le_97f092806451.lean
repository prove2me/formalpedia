-- Prove2me | solution 1 for P2M_GlobalTheory_cohOn_finrank__zero_le_97f092806451
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:33:54.115351+00:00
-- url     : https://prove2.me/submissions/404de648-b7f5-4362-b998-2e06644e9c4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_GlobalTheory_cohOn_injective_zero
import Theorems.Thm_GlobalTheory_SheafLES_injective_zero


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
variable (k : Type v) [Field k] [Algebra k Γ(X, ⊤)]
namespace GlobalTheory.cohOn
theorem _root_.solution (h₂ : Module.Finite k (cohOn S.X₂ U 0)) :
    finrank k (cohOn S.X₁ U 0) ≤ finrank k (cohOn S.X₂ U 0) :=
  LinearMap.finrank_le_finrank_of_injective (injective_zero k hS U)
end GlobalTheory.cohOn
