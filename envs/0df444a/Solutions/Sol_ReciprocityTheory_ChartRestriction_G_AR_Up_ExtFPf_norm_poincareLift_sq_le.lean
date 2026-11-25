-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.norm_poincareLift_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:32:01.583692+00:00
-- url     : https://prove2.me/submissions/f6ef1c7e-b22d-4e2b-8171-a92a3b64e555

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {X} {x0 : Frame X.Ψ r} (D : LUData X x0) (la : Wt X.Ψ r) (F : V (nd X) → ℂ)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
theorem _root_.solution {x : Frame X.Ψ r} (_hx : x ∈ X.dom) {m : ℝ} (hm : 0 < m) (hmx : m ≤ X.nfac la x) :
    ENNReal.ofReal (‖P0 D la F x‖ ^ 2) ≤ ENNReal.ofReal ((m ^ 2)⁻¹) * Gf D la F x := by
  unfold Gf
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 (sq_nonneg m))]
  apply ENNReal.ofReal_le_ofReal
  have hp : X.pnorm la (P0 D la F) x = ‖P0 D la F x‖ * X.nfac la x := rfl
  rw [hp]
  have hm2 : 0 < m ^ 2 := by positivity
  have h1 : m ^ 2 ≤ X.nfac la x ^ 2 := by
    have := hm.le
    gcongr
  have h2 : 1 ≤ (m ^ 2)⁻¹ * X.nfac la x ^ 2 := by
    rw [inv_mul_eq_div, one_le_div hm2]
    exact h1
  rw [mul_pow, ← mul_assoc, mul_comm ((m ^ 2)⁻¹), mul_assoc]
  exact le_mul_of_one_le_right (sq_nonneg _) h2
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
