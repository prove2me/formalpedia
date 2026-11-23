-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.hyperbolic_coeff_a_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:09.444815+00:00
-- url     : https://prove2.me/submissions/3952ddef-d9bf-49ce-abbc-c23aa1bc842e

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
    X.d2a x τ e v = (X.d2q x τ e)⁻¹ * hermC τ.1 X.Gm v (X.Jp x τ e) := rfl
end ReciprocityTheory.ChartRestriction.G.FD.Data
