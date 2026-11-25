-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bound_of_iteratedFDeriv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:17:27.771796+00:00
-- url     : https://prove2.me/submissions/9231a0e0-949b-4380-b86e-ae44fd87385d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_Lemmata_CharacterDirections_Cdir
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IteratedFDerivEqZeroOfIsBigO
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_isBigO_pow_of_iteratedFDeriv_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffOn_of_differentiableOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Asymptotics Metric Set
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} (g : V n → ℂ) (U : Set (V n)) (v0 : V n)
    (hU : IsOpen U) (hv : v0 ∈ U) (hg : DifferentiableOn ℂ g U) (m : ℕ)
    (h : ∀ k ≤ m, iteratedFDeriv ℂ k g v0 = 0) :
    ∃ C : ℝ, ∀ᶠ v in 𝓝 v0, ‖g v‖ ≤ C * ‖v - v0‖ ^ (m + 1) := by
  have hc := contDiffOn_of_differentiableOn n g U hU hg
  have hb := isBigO_pow_of_iteratedFDeriv_zero (m + 1) g U v0 hU hv hc (fun k hk => h k (by omega))
  obtain ⟨C, hC⟩ := isBigO_iff.1 hb
  exact ⟨C, hC.mono fun v hv => by rwa [norm_pow, norm_norm] at hv⟩
end ReciprocityTheory.L2DbarEstimates.Y
