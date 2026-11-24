-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.rit_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:21:10.25303+00:00
-- url     : https://prove2.me/submissions/c79ca565-5321-42d0-ac97-6b11b2cc9a41

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZeroDimA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFderivRightTranslation
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_mulL_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_rit_succ
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_rit_contDiffOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (χ : M2 n → ℂ)
    (hUP : ∀ P x, InP P → x ∈ U → P * x ∈ U) (hl : ∀ P x, InP P → x ∈ U → F (P * x) = χ P * F x) :
    ∀ (N : ℕ) (W : Fin N → M2 n) (P x : M2 n), InP P → x ∈ U → rit F N W (P * x) = χ P * rit F N W x := by
  intro N
  induction N with
  | zero => intro W P x hP hx; exact hl P x hP hx
  | succ N ih =>
    intro W P x hP hx
    rw [rit_succ]
    simp only
    set H := rit F N (fun i => W i.succ) with hH
    have hHs : ContDiffOn ℂ ∞ H U := rit_contDiffOn F U hU hF N _
    have hPx : P * x ∈ U := hUP P x hP hx
    have hdH : DifferentiableAt ℂ H (P * x) :=
      (hHs.contDiffAt (hU.mem_nhds hPx)).differentiableAt (by simp)
    have hev : (fun y => H (P * y)) =ᶠ[nhds x] (fun y => χ P * H y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih _ P y hP hy
    have hc : fderiv ℂ (fun y => H (P * y)) x = (fderiv ℂ H (P * x)).comp (mulL P) := by
      have := (hdH.hasFDerivAt.comp x (mulL P).hasFDerivAt)
      exact this.fderiv
    have hdHx : DifferentiableAt ℂ H x :=
      (hHs.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have e1 : fderiv ℂ H (P * x) (P * x * W 0) = fderiv ℂ (fun y => H (P * y)) x (x * W 0) := by
      rw [hc]; simp [mulL_apply, mul_assoc]
    rw [e1]
    refine (congrArg (fun L : M2 n →L[ℂ] ℂ => L (x * W 0)) hev.fderiv_eq).trans ?_
    have hcm : fderiv ℂ (fun y => χ P * H y) x = χ P • fderiv ℂ H x := fderiv_const_mul hdHx (χ P)
    refine (congrArg (fun L : M2 n →L[ℂ] ℂ => L (x * W 0)) hcm).trans ?_
    simp
end PositivityTheory.Rg.Sw.LVs
