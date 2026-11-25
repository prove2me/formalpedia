-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.std_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:21:38.470918+00:00
-- url     : https://prove2.me/submissions/7dd8a9e0-26a4-4c79-8902-d54275535265

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_SplitProd
import Theorems.Thm_PositivityTheory_ThKG_Std_rad_ne
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_SplitFlip_CondLE_mul
import Theorems.Thm_PositivityTheory_ThKG_Std_ind_ne
import Theorems.Thm_PositivityTheory_ThKG_Std_lc_dl
import Theorems.Thm_PositivityTheory_ThKG_Std_lc_ind
import Theorems.Thm_PositivityTheory_ThKG_Std_lc_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Std
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n d n₁ d₁ : ℕ} {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ}
variable {jr : Fin n₁ → Fin n} {jc : Fin d₁ → Fin d}
namespace PositivityTheory.ThKG.Std
theorem _root_.solution (hϖ : IsUnif ϖ) (hc : 1 ≤ c) (hν : CondLE ϖ c ν) (e : Fin n → Fin d) :
    std ν ϖ c e ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) := by
  refine ⟨(lc_prod _ fun p _ => (lc_ind (rad_ne e p.2)).comp_continuous (continuous_id.matrix_elem _ _)).mul
    ((lc_dl hϖ hc hν).comp_continuous (continuous_id.matrix_submatrix _ _).matrix_det), ?_⟩
  refine HasCompactSupport.intro (isCompact_univ_pi fun _ => isCompact_univ_pi fun j =>
    IsNonarchimedeanLocalField.isCompact_closedBall k (valuation k (rad ϖ c e j))) fun x hx => ?_
  by_contra h
  exact hx fun i _ j _ => ind_ne (Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul h) (i, j) (Finset.mem_univ _))
end PositivityTheory.ThKG.Std
