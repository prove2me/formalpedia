-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Delta_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:48:14.50409+00:00
-- url     : https://prove2.me/submissions/65276dbb-885b-4dfc-abb3-d40ba2370f76

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_diffOn_det
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_Mx_diff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
  Metric
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x0 : Frame X.Ψ r}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
theorem _root_.solution : Differentiable ℂ (DeltaF X x0) := by
  have hdet : ∀ τ (k : Fin (r + 1)), Differentiable ℂ (fun x => lminor (Mx X x0 x τ) k) := by
    intro τ k
    rw [← differentiableOn_univ]
    exact diffOn_det (s := Set.univ)
      (fun x => (Mx X x0 x τ).submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
        (Fin.castLE (Nat.le_of_lt_succ k.isLt)))
      (fun i j => (Mx_diff τ _ _).differentiableOn)
  show Differentiable ℂ (fun x => ∏ τ, ∏ k : Fin (r + 1), lminor (Mx X x0 x τ) k)
  fun_prop
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
