-- Prove2me | solution 1 for P2M_GlobalTheory_cohOn_subsingleton__0c81a4510352
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:34:08.051874+00:00
-- url     : https://prove2.me/submissions/c714fd72-d691-4240-889c-18fc745e71b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_SheafLES_subsingleton__430f6995ae54


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
theorem _root_.solution (h₃ : Subsingleton (cohOn S.X₃ U n))
    (h₂ : Subsingleton (cohOn S.X₂ U (n + 1))) : Subsingleton (cohOn S.X₁ U (n + 1)) :=
  SheafLES.subsingleton₁.{u} (shortExact_toAbSheaf hS) n U h₃ h₂
end GlobalTheory.cohOn
