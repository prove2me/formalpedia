-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.unfoldedDensity_borel_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:44:24.653976+00:00
-- url     : https://prove2.me/submissions/d847cdbc-abb2-4ec5-ad34-df6b2d7c606d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_unfoldedDensity_on_dom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_bchar_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthogonalFrameDomain_rmul_mem_dom


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
theorem _root_.solution {la : Wt X.Ψ r} {f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞}
    (hf : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, f0 (rmul x b) = bchar la b * f0 x)
    (hW : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, W (rmul x b) = W x / ENNReal.ofReal (‖bchar la b‖ ^ 2))
    {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    phi0 X f0 W (rmul x b) = phi0 X f0 W x := by
  rw [unfoldedDensity_on_dom X (OrthogonalFrameDomain.rmul_mem_dom X hx hb), unfoldedDensity_on_dom X hx, hf x hx b hb, hW x hx b hb]
  have hc : bchar la b ≠ 0 := bchar_ne X hb la
  have h0 : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact pow_pos (norm_pos_iff.mpr hc) 2
  rw [norm_mul, mul_pow, ENNReal.ofReal_mul (by positivity)]
  rw [show ENNReal.ofReal (‖bchar la b‖ ^ 2) * ENNReal.ofReal (‖f0 x‖ ^ 2) *
      (W x / ENNReal.ofReal (‖bchar la b‖ ^ 2)) = ENNReal.ofReal (‖f0 x‖ ^ 2) *
      (W x / ENNReal.ofReal (‖bchar la b‖ ^ 2) * ENNReal.ofReal (‖bchar la b‖ ^ 2)) by ring,
    ENNReal.div_mul_cancel h0 ENNReal.ofReal_ne_top]
end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
