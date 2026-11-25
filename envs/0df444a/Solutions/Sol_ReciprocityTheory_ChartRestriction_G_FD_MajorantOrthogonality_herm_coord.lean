-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantOrthogonality.herm_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:57:31.731012+00:00
-- url     : https://prove2.me/submissions/c9fcf595-70ff-487a-a2a3-09548551a461

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_NonvanishingNearMaximum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermCOrthonormalCoordinates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveSpanMatrices
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCombinations
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOrthogonality
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_mem_dom_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IsotropicCombinations_hC_comb2_ortho
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_ortho_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


section
namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantOrthogonality
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
private lemma sum_inv_mulVec_smul_col_of_det_ne_zero (M : Matrix (Fin r) (Fin r) ℂ) (hM : M.det ≠ 0) (w : Fin r → ℂ) :
    ∑ k, (M⁻¹ *ᵥ w) k • col M k = w := by
  have h2 : M *ᵥ (M⁻¹ *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec]
  conv_rhs => rw [← h2]
  funext i
  simp [Matrix.mulVec, dotProduct, col, Finset.sum_apply, mul_comm]
private lemma hermC_col_mat_of_isOrtho (X : Data E r) {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (k l : Fin r) :
    hermC τ.1 X.Gm (col (mat x τ) k) (col (mat x τ) l) =
      if k = l then (if (k : ℕ) < X.p0 then (1 : ℂ) else -1) else 0 := by
  rw [ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.ortho_apply (X := X) ho τ k l]
  by_cases hkl : k = l
  · subst hkl
    by_cases hk : (k : ℕ) < X.p0
    · simp [hk, sgn]
    · simp [hk, sgn]
  · simp [hkl]
end
end ReciprocityTheory.ChartRestriction.G.FD.MajorantOrthogonality
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.MajorantOrthogonality
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantOrthogonality
theorem _root_.solution (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) (τ : X.Ψ)
    (u v : Fin r → E) : τ.1 (herm X.Gm u v) = ReciprocityTheory.MultiplicativeHeights.jForm X.p0
      ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 v) ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 u) := by
  classical
  have hdet : (mat x τ).det ≠ 0 := ((Data.mem_dom_iff X x).mp hx τ).1
  have hf := hermC_col_mat_of_isOrtho X ho τ
  have h1 : τ.1 (herm X.Gm u v) = hermC τ.1 X.Gm (Data.emb τ.1 u) (Data.emb τ.1 v) := by
    simp only [herm, hermC, Data.emb, map_sum, map_mul, cc, IsCMField.complexEmbedding_complexConj]
  calc τ.1 (herm X.Gm u v) = hermC τ.1 X.Gm (Data.emb τ.1 u) (Data.emb τ.1 v) := h1
    _ = hermC τ.1 X.Gm (∑ k, ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 u) k • col (mat x τ) k)
          (∑ l, ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 v) l • col (mat x τ) l) := by
        rw [sum_inv_mulVec_smul_col_of_det_ne_zero (mat x τ) hdet, sum_inv_mulVec_smul_col_of_det_ne_zero (mat x τ) hdet]
    _ = _ := ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations.hC_comb2_ortho τ.1 X.Gm _ hf _ _
end ReciprocityTheory.ChartRestriction.G.FD.MajorantOrthogonality
