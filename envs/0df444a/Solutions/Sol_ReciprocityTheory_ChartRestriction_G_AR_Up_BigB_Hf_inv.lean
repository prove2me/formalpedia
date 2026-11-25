-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.BigB.Hf_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:48:09.153479+00:00
-- url     : https://prove2.me/submissions/72da0505-1aa1-4291-9702-6a4ae355e676

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PointwiseNormInvarianceHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModelNefness
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BigStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_BigB_w_sec
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
namespace BigB
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
private theorem gram_eq_lemma (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (N : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G N = Matrix.transpose N * G.map τ * N.map (starRingEnd ℂ) := by
  ext a c
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
private theorem sum_eq_sum_castLE_of_eq_zero {i : ℕ} (hi : i ≤ r) (f : Fin r → ℂ)
    (hf : ∀ k : Fin r, i ≤ (k : ℕ) → f k = 0) :
    ∑ k, f k = ∑ k : Fin i, f (Fin.castLE hi k) := by
  symm
  exact Fintype.sum_of_injective (Fin.castLE hi) (Fin.castLE_injective hi) _ f
    (fun k hk => hf k (by
      by_contra h
      push_neg at h
      exact hk ⟨⟨k, h⟩, rfl⟩)) (fun _ => rfl)
private theorem submatrix_castLE_transpose_mul_mul_of_triangular {i : ℕ} (hi : i ≤ r) (B A C : Matrix (Fin r) (Fin r) ℂ)
    (hB : ∀ k c : Fin r, c < k → B k c = 0) (hC : ∀ k c : Fin r, c < k → C k c = 0) :
    (Matrix.transpose B * A * C).submatrix (Fin.castLE hi) (Fin.castLE hi) =
      Matrix.transpose (B.submatrix (Fin.castLE hi) (Fin.castLE hi)) *
        A.submatrix (Fin.castLE hi) (Fin.castLE hi) * C.submatrix (Fin.castLE hi) (Fin.castLE hi) := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [sum_eq_sum_castLE_of_eq_zero hi]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [sum_eq_sum_castLE_of_eq_zero hi]
    intro k hk
    have ha := a.isLt
    rw [hB k (Fin.castLE hi a) (by rw [Fin.lt_def, Fin.coe_castLE]; omega), zero_mul]
  · intro l hl
    have hc := c.isLt
    rw [hC l (Fin.castLE hi c) (by rw [Fin.lt_def, Fin.coe_castLE]; omega), mul_zero]
private theorem dmin_rmul_eq_normSq_lminor_mul (X : Data E r) {x b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ)
    (i : Fin (r + 1)) :
    dmin X.Gm (rmul x b) τ i = ((Complex.normSq (lminor (mat b τ) i) : ℝ) : ℂ) * dmin X.Gm x τ i := by
  have hB : ∀ k c : Fin r, c < k → mat b τ k c = 0 := fun k c h => (hb τ).2 k c h
  have hC : ∀ k c : Fin r, c < k → (mat b τ).map (starRingEnd ℂ) k c = 0 := fun k c h => by
    simp [Matrix.map_apply, hB k c h]
  have hm : mat (rmul x b) τ = mat x τ * mat b τ := rfl
  have hdc : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ),
      (M.map (starRingEnd ℂ)).det = starRingEnd ℂ M.det := fun M => (RingHom.map_det _ M).symm
  unfold dmin lminor
  rw [hm, gram_eq_lemma, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul]
  rw [show Matrix.transpose (mat b τ) * Matrix.transpose (mat x τ) * X.Gm.map τ.1 *
      ((mat x τ).map (starRingEnd ℂ) * (mat b τ).map (starRingEnd ℂ)) =
      Matrix.transpose (mat b τ) * (Matrix.transpose (mat x τ) * X.Gm.map τ.1 *
        (mat x τ).map (starRingEnd ℂ)) * (mat b τ).map (starRingEnd ℂ) by simp only [Matrix.mul_assoc]]
  rw [submatrix_castLE_transpose_mul_mul_of_triangular _ _ _ _ hB hC, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.submatrix_map, hdc, ← Complex.mul_conj]
  ring
private theorem rmul_mem_dom_of_mem_bor' (X : Data E r) {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    rmul x b ∈ X.dom := by
  have hd : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  show ∀ τ : X.Ψ, (mat (rmul x b) τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (rmul x b) τ i).re
  intro τ
  have hBt : (mat b τ).BlockTriangular id := fun k c h => (hb τ).2 k c h
  have hdetB : (mat b τ).det ≠ 0 := (hb τ).1
  have hdiag : ∀ j : Fin r, mat b τ j j ≠ 0 := by
    intro j hj
    apply hdetB
    rw [Matrix.det_of_upperTriangular hBt]
    exact Finset.prod_eq_zero (Finset.mem_univ j) hj
  refine ⟨?_, fun i => ?_⟩
  · show (mat x τ * mat b τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hd τ).1 hdetB
  · rw [dmin_rmul_eq_normSq_lminor_mul X hb τ i, Complex.re_ofReal_mul]
    have hpos : 0 < Complex.normSq (lminor (mat b τ) i) := by
      rw [Complex.normSq_pos]
      unfold lminor
      have hBs : ((mat b τ).submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
          (Fin.castLE (Nat.le_of_lt_succ i.isLt))).BlockTriangular id := fun k c h => hBt (by exact h)
      rw [Matrix.det_of_upperTriangular hBs]
      exact Finset.prod_ne_zero_iff.2 fun j _ => hdiag _
    have h1 := (hd τ).2 i
    nlinarith [mul_pos hpos h1]
private theorem ringHom_cc_eq_starRingEnd (τ : E →+* ℂ) (a : E) : τ (cc a) = starRingEnd ℂ (τ a) := by
  unfold cc
  first
  | exact NumberField.IsCMField.complexEmbedding_complexConj τ a
  | exact IsCMField.complexEmbedding_complexConj τ a
  | simp
private theorem sum_mul_mul_cc_eq_of_herm_mulVec {G g : Matrix (Fin r) (Fin r) E}
    (h : ∀ x y, herm G (Matrix.mulVec g x) (Matrix.mulVec g y) = herm G x y) (a b : Fin r) :
    ∑ k, ∑ l, g k a * G k l * cc (g l b) = G a b := by
  have h1 := h (Pi.single a 1) (Pi.single b 1)
  have hs : ∀ c : Fin r, Matrix.mulVec g (Pi.single c (1 : E)) = fun k => g k c := fun c => by
    funext k
    first
    | simp [Matrix.mulVec_single]
    | simp [Matrix.mulVec, Pi.single_apply]
  simp only [hs] at h1
  unfold herm at h1
  rw [h1]
  have hcs : ∀ l : Fin r, cc ((Pi.single b (1 : E) : Fin r → E) l) = (Pi.single b (1 : E) : Fin r → E) l :=
    fun l => by
    by_cases hl : l = b
    · rw [Pi.single_apply, if_pos hl]
      unfold cc
      exact map_one (IsCMField.complexConj E)
    · rw [Pi.single_apply, if_neg hl]
      unfold cc
      exact map_zero (IsCMField.complexConj E)
  simp only [hcs]
  rw [Fintype.sum_eq_single a, Fintype.sum_eq_single b]
  · simp
  · intro l hl
    simp [Pi.single_apply, hl]
  · intro k hk
    simp [Pi.single_apply, hk]
private theorem hermC_mulVec_map_of_gram_invariant (τ : E →+* ℂ) (G g : Matrix (Fin r) (Fin r) E)
    (hg : ∀ a b, ∑ k, ∑ l, g k a * G k l * cc (g l b) = G a b) (u w : Fin r → ℂ) :
    hermC τ G (Matrix.mulVec (g.map τ) u) (Matrix.mulVec (g.map τ) w) = hermC τ G u w := by
  have hM : Matrix.transpose (g.map τ) * G.map τ * (g.map τ).map (starRingEnd ℂ) = G.map τ := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [← hg a b]
    simp only [map_sum, map_mul, ringHom_cc_eq_starRingEnd]
    exact Finset.sum_comm
  have hE : ∀ u w : Fin r → ℂ, hermC τ G u w = u ⬝ᵥ (Matrix.mulVec (G.map τ) (starRingEnd ℂ ∘ w)) := by
    intro u w
    simp only [hermC, Matrix.mulVec, dotProduct, Matrix.map_apply, Function.comp_apply, Finset.mul_sum,
      mul_assoc]
  have hc : starRingEnd ℂ ∘ (Matrix.mulVec (g.map τ) w) =
      Matrix.mulVec ((g.map τ).map (starRingEnd ℂ)) (starRingEnd ℂ ∘ w) := by
    funext i
    exact RingHom.map_mulVec (starRingEnd ℂ) (g.map τ) w i
  rw [hE, hE, hc, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hM, Matrix.dotProduct_mulVec]
private theorem dmin_lact_eq_of_mem_Γ (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (y : Frame X.Ψ r)
    (τ : X.Ψ) (i : Fin (r + 1)) : dmin X.Gm (lact γ y) τ i = dmin X.Gm y τ i := by
  have hK := sum_mul_mul_cc_eq_of_herm_mulVec (X.Γ_stab γ hγ).1
  have hcol : ∀ a, col (mat (lact γ y) τ) a =
      Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (col (mat y τ) a) := fun a => rfl
  have hgr : gram τ.1 X.Gm (mat (lact γ y) τ) = gram τ.1 X.Gm (mat y τ) := by
    ext a c
    simp only [gram, Matrix.of_apply, hcol, hermC_mulVec_map_of_gram_invariant τ.1 X.Gm _ hK]
  unfold dmin
  rw [hgr]
private theorem pnorm_lact_rmul_of_isSec (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : X.pnorm la P (lact γ (rmul x b)) = X.pnorm la P x := by
  have hxb := rmul_mem_dom_of_mem_bor' X hx hb
  have hPv : P (lact γ (rmul x b)) = X.χ la γ * (bchar la b * P x) := by
    rw [hP.2.2 γ hγ _ hxb, hP.2.1 x hx b hb]
  have hχ : ‖X.χ la γ‖ = 1 := by
    obtain ⟨n, hn, h⟩ := X.χ_fin la
    have h1 := congrArg norm (h γ hγ)
    rw [norm_pow, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h1
  have hBt : ∀ τ : X.Ψ, (mat b τ).BlockTriangular id := fun τ k c h => (hb τ).2 k c h
  have hdiag : ∀ (τ : X.Ψ) (j : Fin r), b τ j j ≠ 0 := by
    intro τ j hj
    apply (hb τ).1
    rw [Matrix.det_of_upperTriangular (hBt τ)]
    exact Finset.prod_eq_zero (Finset.mem_univ j) hj
  have hsub : ∀ (τ : X.Ψ) (n : ℕ) (h : n ≤ r),
      ((mat b τ).submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id :=
    fun τ n h k c hkc => hBt τ (by exact hkc)
  have hlm0 : ∀ (τ : X.Ψ) (j : Fin (r + 1)), lminor (mat b τ) j ≠ 0 := by
    intro τ j
    unfold lminor
    rw [Matrix.det_of_upperTriangular (hsub τ _ _)]
    exact Finset.prod_ne_zero_iff.2 fun k _ => hdiag τ _
  have key : ∀ (τ : X.Ψ) (n : ℕ) (hn : n + 1 ≤ r),
      (∏ j : Fin (n + 1), b τ (Fin.castLE hn j) (Fin.castLE hn j)) =
        (∏ j : Fin n, b τ (Fin.castLE (Nat.le_of_succ_le hn) j) (Fin.castLE (Nat.le_of_succ_le hn) j)) *
          b τ ⟨n, hn⟩ ⟨n, hn⟩ := by
    intro τ n hn
    rw [Fin.prod_univ_castSucc]
    rfl
  have hlm : ∀ (τ : X.Ψ) (i : Fin r),
      lminor (mat b τ) i.succ = lminor (mat b τ) i.castSucc * b τ i i := by
    intro τ i
    unfold lminor
    rw [Matrix.det_of_upperTriangular (hsub τ _ _), Matrix.det_of_upperTriangular (hsub τ _ _)]
    exact key τ i i.isLt
  have hratio : ∀ (τ : X.Ψ) (i : Fin r),
      ‖dmin X.Gm (lact γ (rmul x b)) τ i.succ / dmin X.Gm (lact γ (rmul x b)) τ i.castSucc‖ =
        Complex.normSq (b τ i i) * ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ := by
    intro τ i
    have hn0 : Complex.normSq (lminor (mat b τ) i.castSucc) ≠ 0 :=
      (Complex.normSq_pos.2 (hlm0 τ _)).ne'
    rw [dmin_lact_eq_of_mem_Γ X hγ, dmin_lact_eq_of_mem_Γ X hγ, dmin_rmul_eq_normSq_lminor_mul X hb, dmin_rmul_eq_normSq_lminor_mul X hb, hlm, map_mul,
      Complex.ofReal_mul, mul_assoc, mul_div_mul_left _ _ (Complex.ofReal_ne_zero.2 hn0), mul_div_assoc, norm_mul,
      Complex.norm_of_nonneg (Complex.normSq_nonneg _)]
  have hfac : ∀ (z : ℂ) (m : ℤ), z ≠ 0 → ‖z‖ ^ m * (Complex.normSq z) ^ (-(m : ℝ) / 2) = 1 := by
    intro z m hz
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [Complex.normSq_eq_norm_sq, ← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_intCast,
      ← Real.rpow_add hn, show ((m : ℝ) + ((2 : ℕ) : ℝ) * (-(m : ℝ) / 2)) = 0 by push_cast; ring,
      Real.rpow_zero]
  have hbc : ‖bchar la b‖ * ∏ τ, ∏ i : Fin r, Complex.normSq (b τ i i) ^ (-(la τ i : ℝ) / 2) = 1 := by
    unfold bchar
    rw [norm_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro τ _
    rw [norm_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i _
    rw [norm_zpow]
    exact hfac _ _ (hdiag τ i)
  unfold Data.pnorm
  rw [hPv]
  simp only [hratio]
  rw [norm_mul, norm_mul, hχ, one_mul]
  simp only [Real.mul_rpow (Complex.normSq_nonneg _) (norm_nonneg _), Finset.prod_mul_distrib]
  linear_combination (‖P x‖ * ∏ τ, ∏ i : Fin r,
    ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)) * hbc
end BigB
end ReciprocityTheory.ChartRestriction.G.AR.Up
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open ReciprocityTheory.ChartRestriction.G.AR.Up.BigB
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.BigB
theorem _root_.solution (X : Data E r) (Xa : ArchInM X) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    Hf X Xa (lact γ (rmul x b)) = Hf X Xa x := by
  have hw : ∀ k, X.pnorm Xa.L (Xa.w k) (lact γ (rmul x b)) = X.pnorm Xa.L (Xa.w k) x :=
    fun k => pnorm_lact_rmul_of_isSec X Xa.L (w_sec X Xa k) hγ hx hb
  unfold Hf
  rw [pnorm_lact_rmul_of_isSec X _ Xa.et_sec hγ hx hb]
  simp only [hw]
end ReciprocityTheory.ChartRestriction.G.AR.Up.BigB
