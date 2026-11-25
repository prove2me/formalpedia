-- Prove2me | solution 1 for P2M_GlobalTheory_cohOn_finrank__le_dbd168f9d096
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:33:52.100818+00:00
-- url     : https://prove2.me/submissions/76736e09-9dd4-4b78-8788-804ae24768ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_GlobalTheory_ExactSeq_finrank_le
import Theorems.Thm_P2M_GlobalTheory_cohOn_exact__a6c434186df0
import Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__5aa7b67be2da


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
theorem _root_.solution (h₃ : Module.Finite k (cohOn S.X₃ U n))
    (h₂ : Module.Finite k (cohOn S.X₂ U (n + 1))) :
    finrank k (cohOn S.X₁ U (n + 1)) ≤
      finrank k (cohOn S.X₃ U n) + finrank k (cohOn S.X₂ U (n + 1)) :=
  ExactSeq.finrank_le (exact₁ k hS U n)
end GlobalTheory.cohOn
