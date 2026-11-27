-- Prove2me | solution 1 for P2M_GlobalTheory_cohOn_subsingleton__zero_00893b7894e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:52:46.736565+00:00
-- url     : https://prove2.me/submissions/442a475e-9757-4f7f-9676-e0ae2ea42612

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
namespace GlobalTheory.cohOn
theorem _root_.solution (h₂ : Subsingleton (cohOn S.X₂ U 0)) : Subsingleton (cohOn S.X₁ U 0) :=
  (injective_zero ℤ hS U).subsingleton
end GlobalTheory.cohOn
