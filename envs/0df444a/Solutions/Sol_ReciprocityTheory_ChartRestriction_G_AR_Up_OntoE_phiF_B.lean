-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.phiF_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:23:54.129637+00:00
-- url     : https://prove2.me/submissions/d7db981c-c792-48ba-bb56-7b27153188b8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoE_bchar_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoE_phiF_dom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoS_dom_rmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE
open NumberField Complex Matrix Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS
open scoped ComplexConjugate ContDiff ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE
theorem _root_.solution {la : Wt X.Ψ r} {f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞}
    (hf0 : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, f0 (rmul x b) = bchar la b * f0 x)
    (hW : IsMetricW X la W) : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, phiF X f0 W (rmul x b) = phiF X f0 W x := by
  intro x hx b hb
  rw [phiF_dom X f0 W (dom_rmul X hx hb), phiF_dom X f0 W hx, hf0 x hx b hb, hW.2.1 x hx b hb,
    norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
  have hA0 : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos (norm_pos_iff.2 (bchar_ne X la hb)) 2
  have hAt : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.div_eq_inv_mul]
  calc ENNReal.ofReal (‖bchar la b‖ ^ 2) * ENNReal.ofReal (‖f0 x‖ ^ 2) *
        ((ENNReal.ofReal (‖bchar la b‖ ^ 2))⁻¹ * W x)
      = ENNReal.ofReal (‖f0 x‖ ^ 2) * W x *
          (ENNReal.ofReal (‖bchar la b‖ ^ 2) * (ENNReal.ofReal (‖bchar la b‖ ^ 2))⁻¹) := by ring
    _ = ENNReal.ofReal (‖f0 x‖ ^ 2) * W x := by rw [ENNReal.mul_inv_cancel hA0 hAt, mul_one]
end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE
