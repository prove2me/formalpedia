-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fiStep_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:00:48.207424+00:00
-- url     : https://prove2.me/submissions/721d4121-7f1a-4a75-a270-f303137b9448

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourIndep
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fourCoeff_eq_fiG
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fiBox_slices
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fiG_differentiableOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fiSlice_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Set
open scoped Interval
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {Ω : Set (Fin (n + 1) → ℝ)} {h : (Fin (n + 1) → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (tube (n + 1) Ω))
    (hper : ∀ s ∈ tube (n + 1) Ω, ∀ m : Fin (n + 1) → ℤ, h (s + fun k => (m k : ℂ)) = h s)
    (ν : Fin (n + 1) → ℤ) (c : Fin (n + 1) → ℝ) (a : Fin (n + 1)) (β : ℝ)
    (hseg : ∀ t ∈ Set.uIcc (c a) β, Function.update c a t ∈ Ω) :
    fourCoeff h c ν = fourCoeff h (Function.update c a β) ν := by
  have hcont : ∀ d ∈ Ω, Continuous (fun x : Fin (n + 1) → ℝ =>
      fiG h ν (fun k => (x k : ℂ) + (d k : ℂ) * Complex.I)) := by
    intro d hd
    refine (fiG_differentiableOn hh ν).continuousOn.comp_continuous (by fun_prop) (fun x => ?_)
    show (fun k => ((x k : ℂ) + (d k : ℂ) * Complex.I).im) ∈ Ω
    simpa using hd
  have hc : c ∈ Ω := by simpa using hseg (c a) Set.left_mem_uIcc
  have hc' : Function.update c a β ∈ Ω := hseg β Set.right_mem_uIcc
  rw [fourCoeff_eq_fiG, fourCoeff_eq_fiG, fiBox_slices a _ (hcont c hc),
    fiBox_slices a _ (hcont _ hc')]
  congr 1 with y
  exact fiSlice_eq hh hper ν a c β hseg y
end ReciprocityTheory.L2DbarEstimates.Y
