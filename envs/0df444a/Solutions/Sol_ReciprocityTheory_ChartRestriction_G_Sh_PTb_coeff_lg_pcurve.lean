-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.coeff_lg_pcurve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:32:01.859653+00:00
-- url     : https://prove2.me/submissions/86fb10bc-b984-4f6c-976a-18bff774e1d5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_LgCurvePcurve
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CoeffLgPcurveTop
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_coeff_expand_rescale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_pcurve


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
theorem _root_.solution (G : LogFGL v d) {p : ℕ} (hp : p ≠ 0)
    {γ : Fin d → Fin d → PowerSeries C} (hγ : ∀ a, IsCurve v (γ a)) (x : ℕ → Fin d → C) (n : ℕ)
    (hx : ∀ s < n, ∀ b, IsIntV v (x s b)) (a : Fin d) (m : ℕ) :
    PowerSeries.coeff m (G.lgCurve (pcurve G p γ x n) a) = ∑ s ∈ Finset.range n, ∑ b,
      if p ^ s ∣ m then x s b ^ (m / p ^ s) * PowerSeries.coeff (m / p ^ s) (G.lgCurve (γ b) a)
      else 0 := by
  rw [lgCurve_pcurve G hp hγ x n hx a, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [coeff_expand_rescale]
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
