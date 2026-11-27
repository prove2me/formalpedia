-- Prove2me | solution 1 for P2M_GlobalTheory_hdim__le_f17fed8a4980
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:54:40.994161+00:00
-- url     : https://prove2.me/submissions/833196d1-ba62-460f-801e-84f6d6e0b9dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_cohOn_finrank__le_dbd168f9d096

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
variable (k : Type v) [Field k] [Algebra k Γ(X, ⊤)]
  {S : ShortComplex X.Modules} (hS : S.ShortExact)
include hS
namespace GlobalTheory
theorem _root_.solution (n : ℕ) (h₃ : Module.Finite k (coh S.X₃ n))
    (h₂ : Module.Finite k (coh S.X₂ (n + 1))) :
    hdim k S.X₁ (n + 1) ≤ hdim k S.X₃ n + hdim k S.X₂ (n + 1) :=
  cohOn.finrank₁_le hS ⊤ n k h₃ h₂
end GlobalTheory
