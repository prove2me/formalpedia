-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums.isotropicIndex_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:03:13.133826+00:00
-- url     : https://prove2.me/submissions/afae3dc7-dacb-4228-829f-8a521d84af96

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsPerpHermitianReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_SemistableReduction_LatAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicIndexSums
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IsotropicIndexSums_hC_comb_ortho
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IsotropicIndexSums_sum_mul_conj_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IsotropicIndexSums_emb_ne
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



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums
theorem _root_.solution {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (hne : ξ ≠ 0) (τ : X.Ψ) :
    1 ≤ X.p0 ∧ X.p0 < r := by
  obtain ⟨P, hP, hg⟩ := X.signature τ
  set w : Fin r → ℂ := Data.emb τ.1 ξ with hw
  have hw0 : w ≠ 0 := emb_ne hne τ.1
  have hww : hermC τ.1 X.Gm w w = 0 := by
    have e : hermC τ.1 X.Gm w w = τ.1 (herm X.Gm ξ ξ) := by
      simp only [hw, hermC, herm, Data.emb, map_sum, map_mul, cc, IsCMField.complexEmbedding_complexConj]
    rw [e, hξ, map_zero]

  set z : Fin r → ℂ := P⁻¹ *ᵥ w with hz
  have hwz : w = ∑ k, z k • col P k := by
    have h1 : P *ᵥ z = w := by
      rw [hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hP), Matrix.one_mulVec]
    funext a
    rw [← h1]
    simp [Matrix.mulVec, dotProduct, col, Finset.sum_apply, mul_comm]
  have hcol : ∀ k l, hermC τ.1 X.Gm (col P k) (col P l) =
      if k = l then (if (k : ℕ) < X.p0 then 1 else -1) else 0 := by
    intro k l
    have e := congrFun (congrFun hg k) l
    simp only [gram, Matrix.of_apply, Matrix.diagonal_apply, sgn] at e
    rw [e]
    split_ifs <;> simp
  have hj := hC_comb_ortho τ.1 X.Gm (col P) hcol z
  rw [← hwz, hww] at hj
  have hz0 : z ≠ 0 := by
    intro h0
    apply hw0
    rw [hwz, h0]
    simp
  constructor
  · by_contra hlt
    have hp : X.p0 = 0 := by omega
    apply hz0
    apply sum_mul_conj_eq_zero
    have e : ReciprocityTheory.MultiplicativeHeights.jForm X.p0 z z = -∑ a, z a * conj (z a) := by
      rw [ReciprocityTheory.MultiplicativeHeights.jForm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [ReciprocityTheory.MultiplicativeHeights.sgn, hp, Nat.not_lt_zero, if_false]
      ring
    rw [e] at hj
    linear_combination hj
  · by_contra hle
    push Not at hle
    apply hz0
    apply sum_mul_conj_eq_zero
    have e : ReciprocityTheory.MultiplicativeHeights.jForm X.p0 z z = ∑ a, z a * conj (z a) := by
      rw [ReciprocityTheory.MultiplicativeHeights.jForm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [ReciprocityTheory.MultiplicativeHeights.sgn, if_pos (lt_of_lt_of_le a.isLt hle)]
      ring
    rw [e] at hj
    linear_combination -hj
end ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums
