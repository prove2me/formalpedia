-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.flA_leviV_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:00:51.171561+00:00
-- url     : https://prove2.me/submissions/a040b8fe-5b74-4055-81cc-e16dd6c4a4cd

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flA_apply_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flA_wdb_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flA_wd_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_sum_four_comm_bis
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flA_diff_comp_apply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_differentiableAt_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_differentiableAt_wdb
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_eventually_differentiableAt_of_contDiffAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_of_differentiableAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {U : V n → ℂ} {G : V n → V n} {y : V n}
    (hU : ContDiffAt ℝ 2 U (G y)) (hG : ContDiffAt ℂ 2 G y) (ξ : Fin n → ℂ) :
    leviV n (U ∘ G) y ξ = leviV n U (G y) (fun b => fderiv ℂ G y (WithLp.toLp 2 ξ) b) := by
  have hGy : DifferentiableAt ℂ G y := hG.differentiableAt (by simp)
  have hGd : ∀ᶠ v in 𝓝 y, DifferentiableAt ℂ G v :=
    (hG.eventually (by simp)).mono fun v hv => hv.differentiableAt (by simp)
  have hUd : ∀ᶠ v in 𝓝 y, DifferentiableAt ℝ U (G v) :=
    hG.continuousAt.tendsto.eventually (eventually_differentiableAt_of_contDiffAt hU)
  have hev : ∀ k, wdb n k (U ∘ G) =ᶠ[𝓝 y]
      fun v => ∑ b, wdb n b U (G v) * conj (fderiv ℂ G v (bas n k) b) := by
    intro k; filter_upwards [hGd, hUd] with v h1 h2; exact flA_wdb_comp h2 h1 k
  have hA : ∀ b, DifferentiableAt ℝ (fun v => wdb n b U (G v)) y := fun b =>
    (differentiableAt_wdb hU).comp y (hGy.restrictScalars ℝ)
  have hB := flA_diff_comp_apply hG
  have hwd : ∀ j k, wd n j (wdb n k (U ∘ G)) y = ∑ b, (∑ a, wd n a (wdb n b U) (G y) *
      fderiv ℂ G y (bas n j) a) * conj (fderiv ℂ G y (bas n k) b) := by
    intro j k
    have hc : ∀ b, DifferentiableAt ℝ (fun v => conj (fderiv ℂ G v (bas n k) b)) y := fun b =>
      differentiableAt_conj ((hB k b).restrictScalars ℝ)
    rw [wd_congr (hev k), wd_sum Finset.univ
      (f := fun b v => wdb n b U (G v) * conj (fderiv ℂ G v (bas n k) b))
      (fun b _ => (hA b).mul (hc b))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [wd_mul (hA b) (hc b), wd_conj ((hB k b).restrictScalars ℝ),
      wdb_of_differentiableAt (hB k b)]
    rw [show (fun v => wdb n b U (G v)) = wdb n b U ∘ G from rfl,
      flA_wd_comp (differentiableAt_wdb hU) hGy j]
    simp
  simp only [leviV]
  simp_rw [hwd, flA_apply_sum]
  simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [sum_four_comm_bis, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring
end ReciprocityTheory.L2DbarEstimates.Y
