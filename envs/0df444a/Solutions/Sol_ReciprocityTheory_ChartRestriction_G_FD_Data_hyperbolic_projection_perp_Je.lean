-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.hyperbolic_projection_perp_Je
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:48:20.064522+00:00
-- url     : https://prove2.me/submissions/a227dd7e-7fd0-4397-b38c-848a89c74361

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hyperbolic_coeff_a_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hyperbolic_projection_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hermitian_pairing_e_Je
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hermitian_pairing_Je_Je_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_smul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
noncomputable section
section herm
variable {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
private lemma hermC_sub_left_section (u u' v : Fin r → ℂ) :
    hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
end herm
namespace Data
variable {r : ℕ} (X : Data E r)
section perTau
variable (x : Frame X.Ψ r) (τ : X.Ψ) (e : Fin r → ℂ) (δ : (Fin r → ℂ) →ₗ[ℂ] ℂ)
variable {x τ e}
variable (hx : x ∈ X.dom) (he : hermC τ.1 X.Gm e e = 0) (hq : X.d2q x τ e ≠ 0)
include hx he hq
end perTau
end Data
end
end ReciprocityTheory.ChartRestriction.G.FD
end

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
theorem _root_.solution (v : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.d2pi x τ e v) (X.Jp x τ e) = 0 := by
  rw [hyperbolic_projection_apply, hermC_sub_left_section, hermC_sub_left_section, hC_smul_left, hC_smul_left, X.hermitian_pairing_e_Je hx,
    X.hermitian_pairing_Je_Je_zero hx he, hyperbolic_coeff_a_apply, mul_zero, sub_zero, inv_mul_eq_div, div_mul_cancel₀ _ hq, sub_self]
end ReciprocityTheory.ChartRestriction.G.FD.Data
