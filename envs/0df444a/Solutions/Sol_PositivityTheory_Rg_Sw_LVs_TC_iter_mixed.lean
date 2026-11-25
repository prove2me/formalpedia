-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.iter_mixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:55:49.362803+00:00
-- url     : https://prove2.me/submissions/0a553b62-ee1a-44e2-ae72-f8284ab252f6

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCCalc
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_iter_diffAt
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_iter_cast
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_eval_smooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open Set Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) (b : ℕ) (w : Fin b → V) :
    ∀ (a : ℕ) {c : V}, c ∈ Ω → ∀ (u : Fin a → V),
      iteratedFDeriv ℂ a (fun x => iteratedFDeriv ℂ b F x w) c u = iteratedFDeriv ℂ (a + b) F c (Fin.append u w) := by
  intro a
  induction a with
  | zero =>
    intro c hc u
    rw [iteratedFDeriv_zero_apply, iter_cast (zero_add b) (Fin.append u w),
      Fin.append_left_nil u w rfl]
    congr 1
  | succ a ih =>
    intro c hc u
    have hg : ContDiffOn ℂ ∞ (fun x => iteratedFDeriv ℂ b F x w) Ω := eval_smooth hΩ hF b w
    have hd1 := iter_diffAt hΩ hg a hc
    have hd2 := iter_diffAt hΩ hF (a + b) hc
    rw [iteratedFDeriv_succ_apply_left, ← fderiv_continuousMultilinear_apply_const_apply hd1]
    have he : (fun y => iteratedFDeriv ℂ a (fun x => iteratedFDeriv ℂ b F x w) y (Fin.tail u))
        =ᶠ[𝓝 c] (fun y => iteratedFDeriv ℂ (a + b) F y (Fin.append (Fin.tail u) w)) := by
      filter_upwards [hΩ.mem_nhds hc] with y hy
      exact ih hy (Fin.tail u)
    rw [he.fderiv_eq, fderiv_continuousMultilinear_apply_const_apply hd2]
    have hs := iteratedFDeriv_succ_apply_left (𝕜 := ℂ) (f := F) (x := c) (n := a + b)
      (Fin.cons (u 0) (Fin.append (Fin.tail u) w))
    rw [Fin.cons_zero, Fin.tail_cons] at hs
    rw [← hs, iter_cast (show a + 1 + b = a + b + 1 by omega) (Fin.append u w)]
    congr 1
    conv_rhs => rw [← Fin.cons_self_tail u, Fin.append_cons]
    funext i
    simp
end PositivityTheory.Rg.Sw.LVs.TC
