-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.unfoldedDensity_gamma_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:58:28.550879+00:00
-- url     : https://prove2.me/submissions/eb7e572e-b88e-4885-bf29-99dc7e34ed79

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_norm_chi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_unfoldedDensity_on_dom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_lact_mem_dom_iff


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
    (hf : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, f0 (lact γ x) = X.χ la γ * f0 x)
    (hW : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, W (lact γ x) = W x)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    phi0 X f0 W (lact γ x) = phi0 X f0 W x := by
  rw [unfoldedDensity_on_dom X ((lact_mem_dom_iff X hγ x).mpr hx), unfoldedDensity_on_dom X hx, hf γ hγ x hx, hW γ hγ x hx,
    norm_mul, norm_chi X hγ, one_mul]
end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
