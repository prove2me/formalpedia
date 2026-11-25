-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.coefR_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:57.460449+00:00
-- url     : https://prove2.me/submissions/1c3ce672-91b3-4de6-bf33-297e2c8b26a8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpolationModelInequalities
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BasePsiLeviLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CurvatureStatementHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CurvNumStatementPf

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf ReciprocityTheory.L2DbarEstimates Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
theorem _root_.solution {r : ℕ} (X : Data E r) (v : X.Ψ → Fin r → ℝ) (hv : IsDominantR X v) (τ : X.Ψ)
    (a j : Fin r) (h : (a : ℕ) < j) : 0 ≤ coefR X v τ a j := by
  obtain ⟨h1, h2, h3⟩ := hv τ
  have hle : a ≤ j := Fin.le_iff_val_le_val.mpr h.le
  have f1 := fun (hj : (j : ℕ) < X.p0) => h1 a j hle hj
  have f2 := fun (ha : X.p0 ≤ (a : ℕ)) => h2 a j ha hle
  have f3 := fun (ha : (a : ℕ) < X.p0) (hj : X.p0 ≤ (j : ℕ)) => h3 a j ha hj
  unfold coefR Dsg sgn
  split_ifs <;> first
    | (exfalso; omega)
    | (norm_num <;> (first | linarith [f1 (by omega)] | linarith [f2 (by omega)] | linarith [f3 (by omega) (by omega)]))
end ReciprocityTheory.ChartRestriction.G.AR.Up
