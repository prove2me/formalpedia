-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.ind_rmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:58.934802+00:00
-- url     : https://prove2.me/submissions/b73e54b6-45bb-4514-af5a-a02395d07ac7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfB
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
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {x0 : Frame X.Ψ r} (D : ExtFPf.LUData X x0) (FF : Set (V (nd X)))
private theorem gram_eq_lemma (τ' : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (Y : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ' G Y = Yᵀ * G.map τ' * Y.map (starRingEnd ℂ) := by
  ext a c
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm
private theorem transpose_mul_mul_map_cc_eq_of_herm_mulVec (G : Matrix (Fin r) (Fin r) E) (γ : GL (Fin r) E)
    (hγ : ∀ v w : Fin r → E, ReciprocityTheory.ChartRestriction.G.FD.herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v)
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) = ReciprocityTheory.ChartRestriction.G.FD.herm G v w) :
    (γ : Matrix (Fin r) (Fin r) E)ᵀ * G * (γ : Matrix (Fin r) (Fin r) E).map ReciprocityTheory.ChartRestriction.G.FD.cc = G := by
  ext a b
  have hv : ∀ c : Fin r, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (Pi.single c (1 : E) : Fin r → E) =
      fun p => (γ : Matrix (Fin r) (Fin r) E) p c := by
    intro c
    ext p
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hcc : ∀ q : Fin r, ReciprocityTheory.ChartRestriction.G.FD.cc ((Pi.single b (1 : E) : Fin r → E) q) =
      (Pi.single b (1 : E) : Fin r → E) q := by
    intro q
    by_cases hq : q = b
    · subst hq
      simp [ReciprocityTheory.ChartRestriction.G.FD.cc]
    · simp [Pi.single_apply, hq, ReciprocityTheory.ChartRestriction.G.FD.cc]
  have h := hγ (Pi.single a 1) (Pi.single b 1)
  rw [hv, hv] at h
  unfold ReciprocityTheory.ChartRestriction.G.FD.herm at h
  simp only [hcc] at h
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact h.trans (by simp [Pi.single_apply])
private theorem lact_mem_dom' {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact γ x ∈ X.dom := by
  intro τ
  obtain ⟨hxd, hxm⟩ := hx τ
  have hmat : ReciprocityTheory.ChartRestriction.G.FD.mat (lact γ x) τ =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ReciprocityTheory.ChartRestriction.G.FD.mat x τ := rfl
  have hU : ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) = X.Gm.map τ.1 := by
    have h0 := transpose_mul_mul_map_cc_eq_of_herm_mulVec X.Gm γ (X.Γ_stab γ hγ).1
    have hconj : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) =
        ((γ : Matrix (Fin r) (Fin r) E).map ReciprocityTheory.ChartRestriction.G.FD.cc).map τ.1 := by
      ext a b
      simp only [Matrix.map_apply]
      exact (ReciprocityTheory.ChartRestriction.G.FD.emb_cc τ.1 _).symm
    rw [hconj, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h0]
  have hU' : ∀ Y : Matrix (Fin r) (Fin r) ℂ, ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ *
      (X.Gm.map τ.1 * (((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) * Y)) =
      X.Gm.map τ.1 * Y := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU]
  refine ⟨?_, fun i => ?_⟩
  · rw [hmat, Matrix.det_mul]
    refine mul_ne_zero ?_ hxd
    have hdet : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det :=
      (RingHom.map_det _ _).symm
    rw [hdet]
    exact (map_ne_zero τ.1).2 (Matrix.isUnits_det_units γ).ne_zero
  · have hg : ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat (lact γ x) τ) =
        ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) := by
      rw [hmat, gram_eq_lemma, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
      rw [hU']
    have hd : ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (lact γ x) τ i = ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i := by
      unfold ReciprocityTheory.ChartRestriction.G.FD.dmin
      rw [hg]
    rw [hd]
    exact hxm i
private theorem submatrix_castLE_transpose_mul_mul_map_conj_of_upper {i : ℕ} (h : i ≤ r) (B M : Matrix (Fin r) (Fin r) ℂ)
    (hB : ∀ a c : Fin r, c < a → B a c = 0) :
    (Bᵀ * M * B.map (starRingEnd ℂ)).submatrix (Fin.castLE h) (Fin.castLE h) =
      (B.submatrix (Fin.castLE h) (Fin.castLE h))ᵀ * M.submatrix (Fin.castLE h) (Fin.castLE h) *
        (B.submatrix (Fin.castLE h) (Fin.castLE h)).map (starRingEnd ℂ) := by
  have hout : ∀ d : Fin r, d ∉ Set.range (Fin.castLE h) → i ≤ (d : ℕ) := by
    intro d hd
    by_contra hlt
    push_neg at hlt
    exact hd (Set.mem_range.2 ⟨⟨d, hlt⟩, Fin.ext rfl⟩)
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
  · intro d hd
    try dsimp only
    have hlt : Fin.castLE h c < d := by
      show (c : ℕ) < d
      exact lt_of_lt_of_le c.isLt (hout d hd)
    rw [hB d (Fin.castLE h c) hlt, map_zero, mul_zero]
  · intro d'
    try dsimp only
    congr 1
    refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
    · intro k hk
      try dsimp only
      have hlt : Fin.castLE h a < k := by
        show (a : ℕ) < k
        exact lt_of_lt_of_le a.isLt (hout k hk)
      rw [hB k (Fin.castLE h a) hlt, zero_mul]
    · intro k'
      rfl
private theorem exists_pos_lminor_gram_mul_eq (τ' : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (Xm Bm : Matrix (Fin r) (Fin r) ℂ) (hB : ∀ a c : Fin r, c < a → Bm a c = 0)
    (hdiag : ∀ a, Bm a a ≠ 0) (i : Fin (r + 1)) :
    ∃ t : ℝ, 0 < t ∧ ReciprocityTheory.ChartRestriction.G.FD.lminor (ReciprocityTheory.ChartRestriction.G.FD.gram τ' G (Xm * Bm)) i =
      (t : ℂ) * ReciprocityTheory.ChartRestriction.G.FD.lminor (ReciprocityTheory.ChartRestriction.G.FD.gram τ' G Xm) i := by
  have hi : (i : ℕ) ≤ r := Nat.le_of_lt_succ i.isLt
  have hBs : (Bm.submatrix (Fin.castLE hi) (Fin.castLE hi)).det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular (M := Bm.submatrix (Fin.castLE hi) (Fin.castLE hi))
      (fun a c hca => hB (Fin.castLE hi a) (Fin.castLE hi c) hca)]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hdiag _
  refine ⟨Complex.normSq (Bm.submatrix (Fin.castLE hi) (Fin.castLE hi)).det,
    Complex.normSq_pos.2 hBs, ?_⟩
  have hg : ReciprocityTheory.ChartRestriction.G.FD.gram τ' G (Xm * Bm) =
      Bmᵀ * ReciprocityTheory.ChartRestriction.G.FD.gram τ' G Xm * Bm.map (starRingEnd ℂ) := by
    rw [gram_eq_lemma, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  have hc : ((Bm.submatrix (Fin.castLE hi) (Fin.castLE hi)).map (starRingEnd ℂ)).det =
      starRingEnd ℂ (Bm.submatrix (Fin.castLE hi) (Fin.castLE hi)).det :=
    (RingHom.map_det _ _).symm
  unfold ReciprocityTheory.ChartRestriction.G.FD.lminor
  rw [hg, submatrix_castLE_transpose_mul_mul_map_conj_of_upper hi _ _ hB, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc,
    ← Complex.mul_conj]
  ring
private theorem rmul_mem_dom_of_mem_dom {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    rmul x b ∈ X.dom := by
  intro τ
  obtain ⟨hxd, hxm⟩ := hx τ
  obtain ⟨hbd, hbt⟩ := hb τ
  have hB : ∀ a c : Fin r, c < a → ReciprocityTheory.ChartRestriction.G.FD.mat b τ a c = 0 := hbt
  have hdiag : ∀ a : Fin r, ReciprocityTheory.ChartRestriction.G.FD.mat b τ a a ≠ 0 := by
    have h1 := Matrix.det_of_upperTriangular (M := ReciprocityTheory.ChartRestriction.G.FD.mat b τ) hB
    rw [h1] at hbd
    exact fun a => Finset.prod_ne_zero_iff.1 hbd a (Finset.mem_univ a)
  refine ⟨?_, fun i => ?_⟩
  · show (ReciprocityTheory.ChartRestriction.G.FD.mat x τ * ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hxd hbd
  · obtain ⟨t, ht, he⟩ := exists_pos_lminor_gram_mul_eq τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat x τ)
      (ReciprocityTheory.ChartRestriction.G.FD.mat b τ) hB hdiag i
    have he' : ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (rmul x b) τ i =
        (t : ℂ) * ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i := he
    rw [he', Complex.re_ofReal_mul, mul_left_comm]
    exact mul_pos ht (hxm i)
private theorem mem_bor_rmul {b b' : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) :
    rmul b b' ∈ Bor X.Ψ r := by
  intro τ
  obtain ⟨hd, ht⟩ := hb τ
  obtain ⟨hd', ht'⟩ := hb' τ
  refine ⟨?_, fun a c hca => ?_⟩
  · show (ReciprocityTheory.ChartRestriction.G.FD.mat b τ * ReciprocityTheory.ChartRestriction.G.FD.mat b' τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hd hd'
  · show (ReciprocityTheory.ChartRestriction.G.FD.mat b τ * ReciprocityTheory.ChartRestriction.G.FD.mat b' τ) a c = 0
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k a with hk | hk
    · rw [show ReciprocityTheory.ChartRestriction.G.FD.mat b τ a k = 0 from ht a k hk, zero_mul]
    · rw [show ReciprocityTheory.ChartRestriction.G.FD.mat b' τ k c = 0 from ht' k c (lt_of_lt_of_le hca hk), mul_zero]
private theorem FD_mat_inv_mem_bor {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) ∈ Bor X.Ψ r := by
  intro τ
  obtain ⟨hd, ht⟩ := hb τ
  refine ⟨?_, fun a c hca => ?_⟩
  · show ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹).det ≠ 0
    first
      | exact (Matrix.isUnit_nonsing_inv_det _ (Ne.isUnit hd)).ne_zero
      | (rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]; exact inv_ne_zero hd)
  · haveI := (ReciprocityTheory.ChartRestriction.G.FD.mat b τ).invertibleOfIsUnitDet (Ne.isUnit hd)
    have hT : (ReciprocityTheory.ChartRestriction.G.FD.mat b τ).BlockTriangular id := fun a c h => ht a c h
    exact Matrix.blockTriangular_inv_of_blockTriangular hT hca
private theorem rmul_assoc_frame (u v w : Frame X.Ψ r) : rmul (rmul u v) w = rmul u (rmul v w) := by
  funext τ
  exact Matrix.mul_assoc (ReciprocityTheory.ChartRestriction.G.FD.mat u τ) (ReciprocityTheory.ChartRestriction.G.FD.mat v τ) (ReciprocityTheory.ChartRestriction.G.FD.mat w τ)
private theorem rmul_rmul_inv_mat_eq_self {y b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    rmul (rmul y b) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) = y := by
  funext τ
  show ReciprocityTheory.ChartRestriction.G.FD.mat y τ * ReciprocityTheory.ChartRestriction.G.FD.mat b τ * (ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ = y τ
  rw [Matrix.mul_nonsing_inv_cancel_right _ _ (Ne.isUnit (hb τ).1)]
  rfl
private theorem rmul_mem_T_iff {y b : Frame X.Ψ r} (hy : y ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    rmul y b ∈ T D FF ↔ y ∈ T D FF := by
  have hyb : rmul y b ∈ X.dom := rmul_mem_dom_of_mem_dom hb hy
  by_cases hΔ : D.Δ y = 0
  · have hn : ¬ y ∈ T D FF := fun h => (show _ ∧ _ ∧ _ from h).2.1 hΔ
    refine iff_of_false ?_ hn
    intro h
    have hΔ' : D.Δ (rmul y b) ≠ 0 := (show _ ∧ _ ∧ _ from h).2.1
    obtain ⟨hz, hb', he⟩ := D.split _ hyb hΔ'
    have hy' : y = rmul (cpt X x0 (D.zOf (rmul y b)))
        (rmul (D.bOf (rmul y b)) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) := by
      calc y = rmul (rmul y b) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := (rmul_rmul_inv_mat_eq_self hb).symm
        _ = rmul (rmul (cpt X x0 (D.zOf (rmul y b))) (D.bOf (rmul y b))) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) :=
          congrArg (fun w => rmul w (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) he
        _ = _ := rmul_assoc_frame _ _ _
    have h2 := (D.uniq _ hz _ (mem_bor_rmul hb' (FD_mat_inv_mem_bor hb))).1
    rw [← hy'] at h2
    exact h2 hΔ
  · obtain ⟨hz, hb0, he⟩ := D.split y hy hΔ
    have hyb' : rmul y b = rmul (cpt X x0 (D.zOf y)) (rmul (D.bOf y) b) :=
      (congrArg (fun w => rmul w b) he).trans (rmul_assoc_frame _ _ _)
    obtain ⟨hΔ1, hz1, -⟩ := D.uniq _ hz _ (mem_bor_rmul hb0 hb)
    rw [← hyb'] at hΔ1 hz1
    constructor
    · intro h
      have hF : D.zOf (rmul y b) ∈ FF := (show _ ∧ _ ∧ _ from h).2.2
      rw [hz1] at hF
      show _ ∧ _ ∧ _
      exact ⟨hy, hΔ, hF⟩
    · intro h
      have hF : D.zOf y ∈ FF := (show _ ∧ _ ∧ _ from h).2.2
      show _ ∧ _ ∧ _
      refine ⟨hyb, hΔ1, ?_⟩
      rw [hz1]
      exact hF
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {x0 : Frame X.Ψ r} (D : ExtFPf.LUData X x0) (FF : Set (V (nd X)))
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
theorem _root_.solution {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x b : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hb : b ∈ Bor X.Ψ r) {M : Type*} [One M] [Zero M] :
    (T D FF).indicator (1 : Frame X.Ψ r → M) (lact γ⁻¹ (rmul x b)) =
      (T D FF).indicator (1 : Frame X.Ψ r → M) (lact γ⁻¹ x) := by
  have hγi : γ⁻¹ ∈ X.Γ := X.Γ.inv_mem hγ
  have hy : lact γ⁻¹ x ∈ X.dom := lact_mem_dom' hγi hx
  have hlr : lact γ⁻¹ (rmul x b) = rmul (lact γ⁻¹ x) b := by
    funext τ
    dsimp only [lact, rmul, mat]
    exact (Matrix.mul_assoc (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1)
      (Matrix.of (x τ)) (Matrix.of (b τ))).symm
  rw [hlr]
  by_cases h : lact γ⁻¹ x ∈ T D FF
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((rmul_mem_T_iff D FF hy hb).2 h)]
    rfl
  · first
      | rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (fun h' => h ((rmul_mem_T_iff D FF hy hb).1 h'))]
      | rw [Set.indicator_of_not_mem h,
          Set.indicator_of_not_mem (fun h' => h ((rmul_mem_T_iff D FF hy hb).1 h'))]
end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
