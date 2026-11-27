-- Prove2me | solution 1 for P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_comp_real__88522f51eb0a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:16:26.688799+00:00
-- url     : https://prove2.me/submissions/0bffeb0c-afc3-4a7e-831e-5c6c6f2f2ddb

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
open Filter Topology Set
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
theorem _root_.solution (n : ℕ) (j : Fin n) (k : ℝ → ℝ) (p : V n → ℝ) (y : V n)
    (hk : DifferentiableAt ℝ k (p y)) (hp : DifferentiableAt ℝ p y) :
    wdb n j (fun w => ((k (p w) : ℝ) : ℂ)) y = ((deriv k (p y) : ℝ) : ℂ) * wdb n j (fun w => (p w : ℂ)) y := by
  have h1 := Complex.ofRealCLM.hasFDerivAt.comp y (hk.hasDerivAt.comp_hasFDerivAt y hp.hasFDerivAt)
  have h2 := Complex.ofRealCLM.hasFDerivAt.comp y hp.hasFDerivAt
  have e1 : (fun w => ((k (p w) : ℝ) : ℂ)) = ⇑Complex.ofRealCLM ∘ (k ∘ p) := by
    funext w; simp
  have e2 : (fun w => ((p w : ℝ) : ℂ)) = ⇑Complex.ofRealCLM ∘ p := by
    funext w; simp
  rw [e1, e2]
  simp only [wdb]
  rw [h1.fderiv, h2.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul]
  ring
end ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
