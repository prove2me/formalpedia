-- Prove2me | solution 1 for P2M_GlobalTheory_SplitFlip_IsRightTranslationIsometric_cond__7d1c9e0e004a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:34:02.047059+00:00
-- url     : https://prove2.me/submissions/dea05660-ebc8-48c3-a1f4-fe79a3b6b6ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_CondLE_div

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SplitFlip
namespace IsRightTranslationIsometric
theorem _root_.solution {ϖ : kˣ} {ψ : AddChar k Circle} {α β : kˣ →* ℂˣ} {e : ℕ} (h : IsRightTranslationIsometric ϖ ψ α β e) :
    CondLE ϖ e (α / β) := h.condα.div h.condβ
end IsRightTranslationIsometric
end GlobalTheory.SplitFlip
