-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.hermitian_pairing_Je_e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:59.845932+00:00
-- url     : https://prove2.me/submissions/23783e85-f768-4059-825c-249ede60d444

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
variable {x τ e}
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution : hermC τ.1 X.Gm (X.Jp x τ e) e = X.d2q x τ e := rfl
end ReciprocityTheory.ChartRestriction.G.FD.Data
