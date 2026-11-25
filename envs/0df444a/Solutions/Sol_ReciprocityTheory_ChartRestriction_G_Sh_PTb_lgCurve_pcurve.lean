-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_pcurve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:14:30.939799+00:00
-- url     : https://prove2.me/submissions/89da60cf-7ca6-42b1-a52d-e1f7a8304649

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_EqZeroOfVecMulTmat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_LgCurvePcurve
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_isCurve_pcurve
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_isCurve_expC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_isCurve_rescale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_isCurve_sumF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_expC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_rescale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_sumF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution (G : LogFGL v d) {p : ℕ} (hp : p ≠ 0) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (x : ℕ → Fin d → C) :
    ∀ n, (∀ s < n, ∀ b, IsIntV v (x s b)) → ∀ a, G.lgCurve (pcurve G p γ x n) a =
      ∑ s ∈ Finset.range n, ∑ b, PowerSeries.expand (p ^ s) (pow_ne_zero _ hp)
        (PowerSeries.rescale (x s b) (G.lgCurve (γ b) a))
  | 0, _, a => by simp [pcurve, lgCurve_zero]
  | n + 1, hx, a => by
      have hx' : ∀ s < n, ∀ b, IsIntV v (x s b) := fun s hs b => hx s (by omega) b
      have hc : ∀ b, IsCurve v (expC (p ^ n) (rescaleCurve (x n b) (γ b))) := fun b =>
        isCurve_expC (pow_ne_zero _ hp) (isCurve_rescale (hx n (by omega) b) (hγ b))
      rw [pcurve, lgCurve_add G (fun b => (isCurve_pcurve G hp hγ x n hx' b).1)
        (fun b => (isCurve_sumF G _ hc b).1), solution G hp hγ x n hx' a,
        lgCurve_sumF G _ hc, Finset.sum_range_succ]
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [lgCurve_expC G (pow_ne_zero _ hp) (fun c => (isCurve_rescale (hx n (by omega) b) (hγ b) c).1),
        lgCurve_rescale G _ (fun c => (hγ b c).1)]
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
