-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Sh_pt6__551763a68825
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:13:19.638438+00:00
-- url     : https://prove2.me/submissions/ab676375-a3d7-4741-95fa-391091624ec1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TypicalCurveStructureConstants
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CoeffLgPcurveTop
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_GeomSumRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_WtSubOneLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_isCurve_rescale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_isCurve_sumF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_rescale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_sumF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_tangent_eq_lc_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh.PTb
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution : TypicalCurveRebasing := by
  unfold TypicalCurveRebasing
  intro C _ _ _ v p hp hv d m G γ x hc hx
  dsimp only
  have hcr : ∀ u, IsCurve v (rescaleCurve (x u) (γ u)) := fun u => isCurve_rescale (hx u) (hc u)
  have hγ' : IsCurve v (G.sumF fun u => rescaleCurve (x u) (γ u)) := isCurve_sumF G _ hcr
  have hlc : ∀ (k : ℕ) (a : Fin d),
      PowerSeries.coeff k (G.lgCurve (G.sumF fun u => rescaleCurve (x u) (γ u)) a) =
        ∑ u, x u ^ k * PowerSeries.coeff k (G.lgCurve (γ u) a) := by
    intro k a
    rw [lgCurve_sumF G _ hcr a, map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [lgCurve_rescale G (x u) (fun b => (hc u b).1) a, PowerSeries.coeff_rescale]
  have hL : ∀ n : ℕ, G.lc p (G.sumF fun u => rescaleCurve (x u) (γ u)) n =
      ∑ u, x u ^ p ^ n • G.lc p (γ u) n := by
    intro n
    funext a
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, LogFGL.lc]
    exact hlc (p ^ n) a
  refine ⟨hγ', ?_, hL, ?_⟩
  · rw [tangent_eq_lc_zero G p (fun b => (hγ' b).1), hL 0]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [tangent_eq_lc_zero G p (fun b => (hc u b).1), pow_zero, pow_one]
  · intro hT
    unfold LogFGL.IsPTypical at hT ⊢
    intro a k hk
    rw [hlc k a]
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [hT u a k hk, mul_zero]
end ReciprocityTheory.ChartRestriction.G.Sh
