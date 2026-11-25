-- Prove2me | solution 1 for P2M_GlobalTheory_hdim__le_b9cb39bd95c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:41:33.598831+00:00
-- url     : https://prove2.me/submissions/626f48c8-b658-4df3-bed8-a42a9271ca0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_cohOn_finrank__le_0cafa1d92393

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
theorem _root_.solution (n : ℕ) (h₁ : Module.Finite k (coh S.X₁ n)) (h₃ : Module.Finite k (coh S.X₃ n)) :
    hdim k S.X₂ n ≤ hdim k S.X₁ n + hdim k S.X₃ n :=
  cohOn.finrank₂_le hS ⊤ n k h₁ h₃
end GlobalTheory
