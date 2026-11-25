-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.unipotent_fixes_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:29.812152+00:00
-- url     : https://prove2.me/submissions/b1ad81a5-d78f-4b05-a552-180bf97dfa62

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hyperbolic_coeff_b_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_unipotent_mulVec_formula
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hyperbolic_projection_e

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
theorem _root_.solution : Matrix.mulVec (X.d2n x τ e δ) e = e := by
  rw [unipotent_mulVec_formula, X.hyperbolic_projection_e hx he hq, hyperbolic_coeff_b_apply, he]
  simp
end ReciprocityTheory.ChartRestriction.G.FD.Data
