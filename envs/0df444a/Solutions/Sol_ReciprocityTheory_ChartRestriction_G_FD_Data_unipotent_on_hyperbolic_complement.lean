-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.unipotent_on_hyperbolic_complement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:33.890665+00:00
-- url     : https://prove2.me/submissions/5f857fec-a500-4e28-915f-4e92ba501356

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hyperbolic_projection_of_perp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_unipotent_on_orthogonal_e

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
variable (hx : x ∈ X.dom) (he : hermC τ.1 X.Gm e e = 0) (hq : X.d2q x τ e ≠ 0)
include hx he hq
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution {u : Fin r → ℂ} (hu1 : hermC τ.1 X.Gm u e = 0)
    (hu2 : hermC τ.1 X.Gm u (X.Jp x τ e) = 0) :
    Matrix.mulVec (X.d2n x τ e δ) u = u + δ u • e := by
  rw [X.unipotent_on_orthogonal_e δ hx he hq hu1, X.hyperbolic_projection_of_perp hx he hq hu1 hu2]
end ReciprocityTheory.ChartRestriction.G.FD.Data
