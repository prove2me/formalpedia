-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.unipotent_mulVec_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:09.676654+00:00
-- url     : https://prove2.me/submissions/9c7e29c0-cc5a-4287-9863-69fa10a45d76

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
noncomputable section
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
variable (x : Frame X.Ψ r) (τ : X.Ψ) (e : Fin r → ℂ) (δ : (Fin r → ℂ) →ₗ[ℂ] ℂ)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (v : Fin r → ℂ) :
    Matrix.mulVec (X.d2n x τ e δ) v = v + (δ (X.d2pi x τ e v) -
      δ (X.d2z x τ e δ) / 2 * X.d2b x τ e v) • e - X.d2b x τ e v • X.d2z x τ e δ := by
  simp only [d2n, LinearMap.toMatrix'_mulVec]
  rfl
end ReciprocityTheory.ChartRestriction.G.FD.Data
