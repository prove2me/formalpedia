-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.rm_wdb_ofReal_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:24:49.286342+00:00
-- url     : https://prove2.me/submissions/2e905a53-063a-44c5-835a-5e9620606220

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_RegMaxA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y) (k : Fin n) :
    wdb n k (fun x => (F x : ℂ)) =ᶠ[𝓝 y] fun x =>
      (((fderiv ℝ F x (bas n k) : ℝ) : ℂ) +
        Complex.I * ((fderiv ℝ F x (Complex.I • bas n k) : ℝ) : ℂ)) / 2 := by
  filter_upwards [hF.eventually (by simp)] with x hx
  have hd : HasFDerivAt (fun x => (F x : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ F x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (hx.differentiableAt (by norm_num)).hasFDerivAt
  unfold wdb
  rw [hd.fderiv]
  simp
end ReciprocityTheory.L2DbarEstimates.Y
