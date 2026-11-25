-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume.psi_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:38.585053+00:00
-- url     : https://prove2.me/submissions/27d5cbd3-61e0-48c5-ba36-d2d1d5c83607

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeVolume
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCubeVolume_Bv_cont
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCubeVolume_Zb_dom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  (u : Fin 2 → Fin r → E) (g : ℕ) (ω : Fin (4 * Fintype.card X.Ψ) → X.Ψ → Fin 2 → Fin 2 → ℂ)
  (G : Frame X.Ψ r → ℂ)
variable {X u g ω G}
variable (hω : X.IsLZBasis g ω)
  (hadd : ∀ b b' x, X.Zb u b (X.Zb u b' x) = X.Zb u (b + b') x)
  (hdomH : ∀ b, IsHermFam b → ∀ x ∈ X.dom, X.Zb u b x ∈ X.dom)
include hω hdomH
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
theorem _root_.solution (hG : DifferentiableOn ℂ G X.dom) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Continuous fun t => G (X.Zb u (Bv ω t) x) := by
  have hB : Continuous (Bv ω) := Bv_cont ω
  have hc : Continuous fun t => X.Zb u (Bv ω t) x := by
    unfold Data.Zb Data.zmat
    fun_prop
  exact hG.continuousOn.comp_continuous hc (fun t => Zb_dom hω hdomH t hx)
end ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
