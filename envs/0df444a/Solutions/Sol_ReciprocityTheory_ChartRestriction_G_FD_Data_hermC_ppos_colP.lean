-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.hermC_ppos_colP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:28:42.606367+00:00
-- url     : https://prove2.me/submissions/63f09119-cbc1-4485-9a52-91bc71ce26fb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_posDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD
open Matrix NumberField
open scoped ComplexOrder ComplexConjugate
section Herm
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end Herm
section Quad
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end Quad
namespace Data
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private theorem isUnit_det_of_posDef_fundamental_domains {n : Type} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (h : A.PosDef) : IsUnit A.det :=
  isUnit_iff_ne_zero.2 ((Matrix.PosSemidef.posDef_iff_det_ne_zero h.posSemidef).1 h)
end Data
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Matrix NumberField
open scoped ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u : Fin r → ℂ) (d : Fin X.p0) :
    hermC τ.1 X.Gm (X.ppos x τ u) (X.colP x τ d) = hermC τ.1 X.Gm u (X.colP x τ d) := by
  have hA : (X.gramPos x τ)⁻¹ * X.gramPos x τ = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef_fundamental_domains (X.gramPos_posDef hx τ))
  rw [X.ppos_eq x τ u, hermC_sum_left]
  simp_rw [hermC_smul_left, ← X.gramPos_apply x τ, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ← Matrix.mul_apply, hA, Matrix.one_apply]
  simp
end ReciprocityTheory.ChartRestriction.G.FD.Data
