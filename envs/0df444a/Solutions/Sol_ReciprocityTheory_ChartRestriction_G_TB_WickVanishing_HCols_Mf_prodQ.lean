-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols.Mf_prodQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:24:29.142405+00:00
-- url     : https://prove2.me/submissions/7d325ab5-3781-49fa-9e4c-6b6dcda3cf2d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSCCols
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LemmaH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LemmaHCols
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_Mf_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_Mf_monomial
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_colM_combine
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_prodQ_monomial
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_nablaL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.TB.SCPf.nablaL_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols
variable {k : Type} [CommRing k] {ι : Type} [Fintype ι] {n : ℕ}
variable (mu : Fin n → MvPolynomial ι k →ₗ[k] k)
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols
theorem _root_.solution (R : Fin n → MvPolynomial ι k) : Mf mu (prodQ R) = ∏ b, mu b (R b) := by
  classical
  have hR : ∀ b, colE b (R b) = ∑ α ∈ (R b).support, colE b (monomial α (coeff α (R b))) := by
    intro b
    conv_lhs => rw [as_sum (R b)]
    rw [map_sum]
  have hmu : ∀ b, mu b (R b) = ∑ α ∈ (R b).support, coeff α (R b) * mu b (monomial α 1) := by
    intro b
    conv_lhs => rw [as_sum (R b)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun α _ => by
      rw [show monomial α (coeff α (R b)) = coeff α (R b) • monomial α (1 : k) by
        rw [smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  rw [prodQ, Finset.prod_congr rfl (fun b _ => hR b), Finset.prod_univ_sum, Mf_sum,
    Finset.prod_congr rfl (fun b _ => hmu b), Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hp := prodQ_monomial x (fun b => coeff (x b) (R b))
  simp only [prodQ] at hp
  rw [hp, Mf_monomial, Finset.prod_mul_distrib]
  simp only [colM_combine]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols
