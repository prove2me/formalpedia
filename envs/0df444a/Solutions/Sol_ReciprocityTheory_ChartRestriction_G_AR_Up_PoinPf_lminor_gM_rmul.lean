-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.lminor_gM_rmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:57.365441+00:00
-- url     : https://prove2.me/submissions/44612319-1123-4bf9-98f9-6f5679a6bef4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_lminor_mul_upper
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_gM_rmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
theorem _root_.solution (X : Data E r) (x0 y : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (τ : X.Ψ) (i : Fin (r + 1)) :
    lminor (gM X x0 (rmul y b) τ) i = lminor (gM X x0 y τ) i * ∏ j : Fin i,
      mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
  rw [gM_rmul]
  exact lminor_mul_upper _ _ (fun a c h => (hb τ).2 a c h) i
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
