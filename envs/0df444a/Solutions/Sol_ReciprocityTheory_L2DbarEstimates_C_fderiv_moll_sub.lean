-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.fderiv_moll_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:05.254364+00:00
-- url     : https://prove2.me/submissions/c74d902a-3c53-4bf4-9f43-e21a831f36a6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegConv
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_contDiff_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {n : ℕ} {t : ℝ} (x y w : V n) :
    fderiv ℝ (fun y => ((moll n t (x - y) : ℝ) : ℂ)) y w
      = -((fderiv ℝ (moll n t) (x - y) w : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ (moll n t) (x - y) :=
    (moll_contDiff_one n t).differentiable one_ne_zero (x - y)
  have h1 : HasFDerivAt (fun y : V n => x - y) (-ContinuousLinearMap.id ℝ (V n)) y :=
    (hasFDerivAt_id y).const_sub x
  have h2 := Complex.ofRealCLM.hasFDerivAt.comp y (hd.hasFDerivAt.comp y h1)
  rw [show (fun y => ((moll n t (x - y) : ℝ) : ℂ)) =
    Complex.ofRealCLM ∘ (moll n t ∘ fun y => x - y) from rfl, h2.fderiv]
  simp
end ReciprocityTheory.L2DbarEstimates.C
