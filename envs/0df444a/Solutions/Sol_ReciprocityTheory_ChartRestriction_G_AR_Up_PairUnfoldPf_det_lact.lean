-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.det_lact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:33:32.057796+00:00
-- url     : https://prove2.me/submissions/26c3957b-0153-455e-b69e-8689f4d27800

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_mat_lact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
theorem _root_.solution (γ : GL (Fin r) E) (x : Frame X.Ψ r) (τ : X.Ψ) :
    (mat (lact γ x) τ).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det * (mat x τ).det := by
  rw [mat_lact, Matrix.det_mul, RingHom.map_det]
  rfl
end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
