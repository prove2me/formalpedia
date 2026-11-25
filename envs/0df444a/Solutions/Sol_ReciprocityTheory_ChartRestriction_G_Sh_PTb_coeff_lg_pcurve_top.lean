-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.coeff_lg_pcurve_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:44:46.076249+00:00
-- url     : https://prove2.me/submissions/eeb8eea9-3a6a-4ccf-b5da-83a51cd3a8b3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_LgCurvePcurve
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CoeffLgPcurveTop
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_coeff_lg_pcurve

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
theorem _root_.solution (G : LogFGL v d) {p : ℕ} (hp : p.Prime)
    {γ : Fin d → Fin d → PowerSeries C} (hγ : ∀ a, IsCurve v (γ a)) (x : ℕ → Fin d → C) (n : ℕ)
    (hx : ∀ s < n, ∀ b, IsIntV v (x s b)) (a : Fin d) :
    PowerSeries.coeff (p ^ n) (G.lgCurve (pcurve G p γ x n) a) =
      (∑ s ∈ Finset.range n, ∑ b, (x s b) ^ (p ^ (n - s)) • G.lc p (γ b) (n - s)) a := by
  rw [coeff_lg_pcurve G hp.ne_zero hγ x n hx a (p ^ n)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro s hs
  have hsn : s ≤ n := (Finset.mem_range.mp hs).le
  apply Finset.sum_congr rfl
  intro b _
  rw [if_pos (pow_dvd_pow p hsn), Nat.pow_div hsn hp.pos]
  rfl
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
