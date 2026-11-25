-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.isCurve_pcurve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:56:39.260098+00:00
-- url     : https://prove2.me/submissions/63ac008d-5557-45a2-bdc1-12116fb8e4e2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_EqZeroOfVecMulTmat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_LgCurvePcurve
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_isCurve_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_isCurve_expC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_isCurve_rescale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_isCurve_sumF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_isCurve_zero


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
    ∀ n, (∀ s < n, ∀ b, IsIntV v (x s b)) → IsCurve v (pcurve G p γ x n)
  | 0, _ => isCurve_zero
  | n + 1, hx => isCurve_add G (solution G hp hγ x n fun s hs b => hx s (by omega) b)
      (isCurve_sumF G _ fun b => isCurve_expC (pow_ne_zero _ hp)
        (isCurve_rescale (hx n (by omega) b) (hγ b)))
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
