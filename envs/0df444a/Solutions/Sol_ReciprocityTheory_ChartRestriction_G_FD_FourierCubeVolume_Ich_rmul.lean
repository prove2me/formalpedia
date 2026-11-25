-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume.Ich_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:13.382717+00:00
-- url     : https://prove2.me/submissions/9e4077fd-f1aa-4029-95b9-7376e1590aeb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeVolume
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCubeVolume_Zb_dom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientMatrices_mat_Zb


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
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
theorem _root_.solution (la : Wt X.Ψ r) (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = bchar la b * G x)
    (hω : X.IsLZBasis g ω) (hdomH : ∀ b, IsHermFam b → ∀ x ∈ X.dom, X.Zb u b x ∈ X.dom)
    (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : Ich X u ω G χ (rmul x b) = bchar la b * Ich X u ω G χ x := by
  have hcomm : ∀ t, X.Zb u (Bv ω t) (rmul x b) = rmul (X.Zb u (Bv ω t) x) b := by
    intro t
    funext τ
    show X.zmat u (Bv ω t) τ * mat (rmul x b) τ = mat (X.Zb u (Bv ω t) x) τ * mat b τ
    change X.zmat u (Bv ω t) τ * (mat x τ * mat b τ) = _
    rw [mat_Zb, Matrix.mul_assoc]
  unfold Ich
  simp_rw [hcomm]
  have h2 : ∀ t, G (rmul (X.Zb u (Bv ω t) x) b) * ech ω χ t = bchar la b * (G (X.Zb u (Bv ω t) x) * ech ω χ t) := by
    intro t
    rw [hB _ (Zb_dom hω hdomH t hx) b hb, mul_assoc]
  simp_rw [h2]
  exact integral_const_mul _ _
end ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
