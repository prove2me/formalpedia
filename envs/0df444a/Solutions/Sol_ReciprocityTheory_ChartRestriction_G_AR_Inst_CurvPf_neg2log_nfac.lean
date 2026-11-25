-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.neg2log_nfac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:31:00.785435+00:00
-- url     : https://prove2.me/submissions/4ae27dd8-4bbe-4450-8cee-a9cca3f4aca7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetSubMapConj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviFinsetSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates ReciprocityTheory.AnForm Filter Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution (la : Wt X.Ψ r) (x : Frame X.Ψ r) (hx : ∀ τ i, dmin X.Gm x τ i ≠ 0) :
    -2 * Real.log (X.nfac la x) = ∑ τ, ∑ i : Fin r, (la τ i : ℝ) *
      (Real.log ‖dmin X.Gm x τ i.succ‖ - Real.log ‖dmin X.Gm x τ i.castSucc‖) := by
  unfold Data.nfac
  have hpos : ∀ τ (i : Fin r), 0 < ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ :=
    fun τ i => norm_pos_iff.2 (div_ne_zero (hx _ _) (hx _ _))
  rw [Real.log_prod (fun τ _ => (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hpos τ i) _).ne'),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (hpos τ i) _).ne'), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_rpow (hpos τ i), norm_div, Real.log_div (norm_ne_zero_iff.2 (hx _ _)) (norm_ne_zero_iff.2 (hx _ _))]
  ring
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
