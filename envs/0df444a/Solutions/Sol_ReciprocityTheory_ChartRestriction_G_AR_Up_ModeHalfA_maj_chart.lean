-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfA.maj_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:35:59.176462+00:00
-- url     : https://prove2.me/submissions/cbd5cbc9-555f-443d-ab34-37640313c4c9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CompactEntryBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfA
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


section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
namespace ModeHalfA
open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
private lemma hermC_eq_dotProduct_upper_bounds (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) :
    hermC τ G u v = u ⬝ᵥ (G.map τ *ᵥ fun b => conj (v b)) := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, mul_assoc]
private lemma gram_eq_upper_bounds (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (Y : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G Y = Yᵀ * G.map τ * Y.map conj := by
  ext i j
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col,
    Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
private lemma hermC_mulVec_eq_dotProduct_gram (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (Y : Matrix (Fin r) (Fin r) ℂ) (w n : Fin r → ℂ) :
    hermC τ G (Y *ᵥ w) (Y *ᵥ n) = w ⬝ᵥ (gram τ G Y *ᵥ fun b => conj (n b)) := by
  have hc : (fun b => conj ((Y *ᵥ n) b)) = Y.map conj *ᵥ fun b => conj (n b) := by
    funext b
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [hermC_eq_dotProduct_upper_bounds, hc, gram_eq_upper_bounds, dotProduct_comm, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, dotProduct_comm, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
private lemma det_ne_zero_of_gram_eq_diagonal_sgn (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ)
    (Y : Matrix (Fin r) (Fin r) ℂ)
    (hY : gram τ G Y = diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) : Y.det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det hY
  rw [gram_eq_upper_bounds, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
    Matrix.det_diagonal] at h1
  exact (Finset.prod_ne_zero_iff.mpr fun a _ => by unfold sgn; split_ifs <;> norm_num) h1.symm
end ModeHalfA
end ReciprocityTheory.ChartRestriction.G.AR.Up
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfA
open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfA
theorem _root_.solution (X : Data E r) {w : Frame X.Ψ r} {τ : X.Ψ} {Y : Matrix (Fin r) (Fin r) ℂ}
    (hY : FD.gram τ.1 X.Gm Y = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (N : Fin r → Fin r → ℂ) (hw : mat w τ = Y * Matrix.of N) (v : Fin r → ℂ) :
    X.maj w τ v = Ms X.p0 X.p0_le N (Y⁻¹ *ᵥ v) := by
  have hS : ∀ u' n : Fin r → ℂ, hermC τ.1 X.Gm (Y *ᵥ u') (Y *ᵥ n) = sf X.p0 u' n := by
    intro u' n
    rw [hermC_mulVec_eq_dotProduct_gram, hY]
    simp only [sf, dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hdetY := det_ne_zero_of_gram_eq_diagonal_sgn τ.1 X.Gm X.p0 Y hY
  have hv : v = Y *ᵥ (Y⁻¹ *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetY), Matrix.one_mulVec]
  have hcol : ∀ a, FD.col (mat w τ) a = Y *ᵥ cl N a := by
    intro a
    rw [hw]
    funext k
    simp [ReciprocityTheory.ChartRestriction.G.FD.col, cl, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hgp : X.gramPos w τ = Ag X.p0 X.p0_le N := by
    ext a b
    simp only [Data.gramPos, Matrix.submatrix_apply, ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, Ag]
    rw [hcol, hcol, hS]
  unfold Data.maj Data.posPart Ms
  rw [hgp]
  conv_lhs => rw [hv]
  simp only [hcol, hS]
end ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfA
