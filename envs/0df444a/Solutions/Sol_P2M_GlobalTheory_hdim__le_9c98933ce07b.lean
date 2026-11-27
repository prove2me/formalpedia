-- Prove2me | solution 1 for P2M_GlobalTheory_hdim__le_9c98933ce07b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:53:19.918724+00:00
-- url     : https://prove2.me/submissions/d7908de4-347f-4f5e-9674-73a2d3576fa8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_cohOn_finrank__le_2b3e184890cd

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
theorem _root_.solution (n : ℕ) (h₂ : Module.Finite k (coh S.X₂ n))
    (h₁ : Module.Finite k (coh S.X₁ (n + 1))) :
    hdim k S.X₃ n ≤ hdim k S.X₂ n + hdim k S.X₁ (n + 1) :=
  cohOn.finrank₃_le hS ⊤ n k h₂ h₁
end GlobalTheory
