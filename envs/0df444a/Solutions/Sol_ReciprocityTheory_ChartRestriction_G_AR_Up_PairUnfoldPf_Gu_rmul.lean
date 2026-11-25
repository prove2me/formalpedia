-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.Gu_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:42:33.145232+00:00
-- url     : https://prove2.me/submissions/fc7f6e68-8dbd-4481-b4f9-4ea795e9e8da

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_Gu_dom
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
theorem _root_.solution {la : Wt X.Ψ r} {P f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞}
    (hP : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x)
    (hf : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, f0 (rmul x b) = bchar la b * f0 x)
    (hW : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, W (rmul x b) = W x / ENNReal.ofReal (‖bchar la b‖ ^ 2))
    {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    Gu X P f0 W (rmul x b) = Gu X P f0 W x := by
  rw [Gu_dom X (OrthogonalFrameDomain.rmul_mem_dom X hx hb), Gu_dom X hx, hP x hx b hb, hf x hx b hb, hW x hx b hb]
  have hc : bchar la b ≠ 0 := bchar_ne X hb la
  have hn : (‖bchar la b‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hc
  have hcc : bchar la b * (starRingEnd ℂ) (bchar la b) = (‖bchar la b‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (by positivity), map_mul]
  push_cast
  rw [show bchar la b * P x * ((starRingEnd ℂ) (bchar la b) * (starRingEnd ℂ) (f0 x)) *
      (((W x).toReal : ℂ) / (‖bchar la b‖ : ℂ) ^ 2) = (bchar la b * (starRingEnd ℂ) (bchar la b)) *
      (P x * (starRingEnd ℂ) (f0 x) * ((W x).toReal : ℂ)) / (‖bchar la b‖ : ℂ) ^ 2 by ring, hcc]
  field_simp
end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
