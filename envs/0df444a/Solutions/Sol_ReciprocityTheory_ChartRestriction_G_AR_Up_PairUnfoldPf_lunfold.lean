-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.lunfold
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:43.323659+00:00
-- url     : https://prove2.me/submissions/1030f3cd-ad35-42df-ada8-d23ea7c90924

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_lunfold_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_mul_mem
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
private theorem continuous_cpt_apply (y0 : Frame X.Ψ r) : Continuous fun z => cpt X y0 z := by
  unfold ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ReciprocityTheory.ChartRestriction.G.FD.rmul ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat
    ReciprocityTheory.ChartRestriction.G.FD.mat
  refine continuous_pi fun τ => ?_
  refine Continuous.matrix_mul continuous_const ?_
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.of_apply]
  split_ifs
  · first
      | fun_prop
      | exact (EuclideanSpace.proj _).continuous
  · exact continuous_const
  · exact continuous_const
private theorem lact_inv_apply_lact (γ : GL (Fin r) E) (y : Frame X.Ψ r) : lact γ⁻¹ (lact γ y) = y := by
  funext τ
  show ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * Matrix.of (y τ)) = y τ
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  rfl
private theorem continuous_FD_dmin (X : Data E r) (τ : X.Ψ) (i : Fin (r + 1)) :
    Continuous fun x : Frame X.Ψ r => ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i := by
  unfold ReciprocityTheory.ChartRestriction.G.FD.dmin ReciprocityTheory.ChartRestriction.G.FD.lminor ReciprocityTheory.ChartRestriction.G.FD.gram
    ReciprocityTheory.ChartRestriction.G.FD.hermC ReciprocityTheory.ChartRestriction.G.FD.col ReciprocityTheory.ChartRestriction.G.FD.mat
  refine Continuous.matrix_det ?_
  refine Continuous.matrix_submatrix ?_ _ _
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.of_apply]
  refine continuous_finset_sum _ fun c _ => continuous_finset_sum _ fun d _ => ?_
  refine Continuous.mul (Continuous.mul ?_ continuous_const) ?_
  · exact (continuous_apply _).comp ((continuous_apply _).comp (continuous_apply τ))
  · exact Complex.continuous_conj.comp
      ((continuous_apply _).comp ((continuous_apply _).comp (continuous_apply τ)))
private theorem isOpen_dom_of_data (X : Data E r) : IsOpen X.dom := by
  show IsOpen {x : Frame X.Ψ r | ∀ τ : X.Ψ, (ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0 ∧
    ∀ i : Fin (r + 1), 0 < ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i * (ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i).re}
  simp only [Set.setOf_forall, Set.setOf_and]
  refine isOpen_iInter_of_finite fun τ => ?_
  refine IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · refine isOpen_ne_fun (Continuous.matrix_det ?_) continuous_const
    unfold ReciprocityTheory.ChartRestriction.G.FD.mat
    exact continuous_apply τ
  · exact isOpen_lt continuous_const
      (continuous_const.mul (Complex.continuous_re.comp (continuous_FD_dmin X τ i)))
private theorem measurableSet_T (hF : MeasurableSet FF) : MeasurableSet (T D FF) := by
  classical
  have hUo : IsOpen {x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0} :=
    (isOpen_dom_of_data X).inter (isOpen_ne_fun D.hΔ.continuous continuous_const)
  have hpw : Measurable ({x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0}.piecewise D.zOf fun _ => 0) :=
    D.hz.continuousOn.measurable_piecewise continuousOn_const hUo.measurableSet
  have hT : T D FF = {x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0} ∩
      ({x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0}.piecewise D.zOf fun _ => 0) ⁻¹' FF := by
    ext x
    constructor
    · intro h
      obtain ⟨h1, h2, h3⟩ := (show _ ∧ _ ∧ _ from h)
      refine ⟨⟨h1, h2⟩, ?_⟩
      show ({x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0}.piecewise D.zOf fun _ => 0) x ∈ FF
      rw [Set.piecewise_eq_of_mem _ _ _
        (show x ∈ {x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0} from ⟨h1, h2⟩)]
      exact h3
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have h3' : ({x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0}.piecewise D.zOf fun _ => 0) x ∈ FF := h3
      rw [Set.piecewise_eq_of_mem _ _ _
        (show x ∈ {x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0} from ⟨h1, h2⟩)] at h3'
      show _ ∧ _ ∧ _
      exact ⟨h1, h2, h3'⟩
  rw [hT]
  exact hUo.measurableSet.inter (hpw hF)
private theorem measurable_lact (γ : GL (Fin r) E) : Measurable fun x : Frame X.Ψ r => lact γ x := by
  refine Continuous.measurable ?_
  unfold lact ReciprocityTheory.ChartRestriction.G.FD.mat
  exact continuous_pi fun τ => Continuous.matrix_mul continuous_const (continuous_apply τ)
private theorem ae_mem_omF (y0 : Frame X.Ψ r) : ∀ᵐ z ∂muF X y0, z ∈ OmF X y0 := by
  have hOm : MeasurableSet (OmF X y0) :=
    ((isOpen_dom_of_data X).preimage (continuous_cpt_apply y0)).measurableSet
  have hac : muF X y0 ≪ volume.restrict (OmF X y0) := by
    unfold ReciprocityTheory.ChartRestriction.G.AR.Up.muF
    exact withDensity_absolutelyContinuous _ _
  exact hac.ae_le (ae_restrict_mem hOm)
private theorem lact_mul_upper_bounds (a b : GL (Fin r) E) (x : Frame X.Ψ r) :
    lact (a * b) x = lact a (lact b x) := by
  funext τ
  dsimp only [lact, mat]
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
  try rfl
private theorem lact_rmul_eq_rmul_lact (g : GL (Fin r) E) (y c : Frame X.Ψ r) :
    lact g (rmul y c) = rmul (lact g y) c := by
  funext τ
  dsimp only [lact, rmul, mat]
  exact (Matrix.mul_assoc ((g : Matrix (Fin r) (Fin r) E).map τ.1) (Matrix.of (y τ))
    (Matrix.of (c τ))).symm
private theorem eq_of_lact_inv_cpt_mem_T (hFF : IsFundSet X x0 FF) {z : V (nd X)} (hz : z ∈ OmF X x0)
    {γ1 γ2 : GL (Fin r) E} (h1 : γ1 ∈ X.Γ) (h2 : γ2 ∈ X.Γ)
    (hT1 : lact γ1⁻¹ (cpt X x0 z) ∈ T D FF) (hT2 : lact γ2⁻¹ (cpt X x0 z) ∈ T D FF) : γ1 = γ2 := by
  obtain ⟨y1, hy1⟩ : ∃ y, y = lact γ1⁻¹ (cpt X x0 z) := ⟨_, rfl⟩
  obtain ⟨y2, hy2⟩ : ∃ y, y = lact γ2⁻¹ (cpt X x0 z) := ⟨_, rfl⟩
  rw [← hy1] at hT1
  rw [← hy2] at hT2
  obtain ⟨hd1, hΔ1, hF1⟩ := (show _ ∧ _ ∧ _ from hT1)
  obtain ⟨hd2, hΔ2, hF2⟩ := (show _ ∧ _ ∧ _ from hT2)
  obtain ⟨hO1, hB1, he1⟩ := D.split y1 hd1 hΔ1
  obtain ⟨hO2, hB2, he2⟩ := D.split y2 hd2 hΔ2
  have hx1 : lact γ1 y1 = cpt X x0 z := by
    have h := lact_inv_apply_lact γ1⁻¹ (cpt X x0 z)
    rw [inv_inv] at h
    rw [hy1]
    exact h
  have hg : (γ2⁻¹ * γ1) ∈ X.Γ := X.Γ.mul_mem (X.Γ.inv_mem h2) h1
  have hEq : cpt X x0 (D.zOf y2) = lact (γ2⁻¹ * γ1) (rmul (cpt X x0 (D.zOf y1)) (rmul (D.bOf y1) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r))) := by
    calc cpt X x0 (D.zOf y2) = rmul (rmul (cpt X x0 (D.zOf y2)) (D.bOf y2)) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := (rmul_rmul_inv_mat_eq_self hB2).symm
      _ = rmul y2 (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := by rw [← he2]
      _ = rmul (lact γ2⁻¹ (lact γ1 y1)) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := by rw [hx1, hy2]
      _ = rmul (lact (γ2⁻¹ * γ1) y1) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := by rw [lact_mul_upper_bounds]
      _ = rmul (lact (γ2⁻¹ * γ1) (rmul (cpt X x0 (D.zOf y1)) (D.bOf y1))) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := by rw [← he1]
      _ = lact (γ2⁻¹ * γ1) (rmul (rmul (cpt X x0 (D.zOf y1)) (D.bOf y1)) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) := (lact_rmul_eq_rmul_lact _ _ _).symm
      _ = lact (γ2⁻¹ * γ1) (rmul (cpt X x0 (D.zOf y1)) (rmul (D.bOf y1) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r))) :=
        congrArg (lact (γ2⁻¹ * γ1)) (rmul_assoc_frame _ _ _)
  have hw : D.zOf y1 = D.zOf y2 :=
    hFF.2.2.1 _ hF1 _ hF2 _ hg _ (mem_bor_rmul hB1 (FD_mat_inv_mem_bor hB2)) hEq
  have hB' : lact (γ2⁻¹ * γ1) y1 = y2 := by rw [lact_mul_upper_bounds, hx1, hy2]
  have hfree : lact (γ2⁻¹ * γ1) (cpt X x0 (D.zOf y1)) = rmul (cpt X x0 (D.zOf y1)) (rmul (D.bOf y2) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y1) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) := by
    calc lact (γ2⁻¹ * γ1) (cpt X x0 (D.zOf y1)) = rmul (rmul (lact (γ2⁻¹ * γ1) (cpt X x0 (D.zOf y1))) (D.bOf y1)) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y1) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) :=
          (rmul_rmul_inv_mat_eq_self hB1).symm
      _ = rmul (lact (γ2⁻¹ * γ1) (rmul (cpt X x0 (D.zOf y1)) (D.bOf y1))) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y1) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := by
        first
          | rw [lact_rmul_eq_rmul_lact]
          | exact congrArg (fun w => rmul w _) (lact_rmul_eq_rmul_lact _ _ _).symm
      _ = rmul (rmul (cpt X x0 (D.zOf y2)) (D.bOf y2)) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y1) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := by rw [← he1, hB', ← he2]
      _ = rmul (cpt X x0 (D.zOf y1)) (rmul (D.bOf y2) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y1) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) := by
        rw [← hw]
        exact rmul_assoc_frame _ _ _
  have h1' := X.Γ_free _ hg _ hO1 _ (mem_bor_rmul hB2 (FD_mat_inv_mem_bor hB1)) hfree
  exact (inv_mul_eq_one.1 h1').symm
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
include D
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
theorem _root_.solution (hM : MeasInvStatement (E := E)) (hx0 : IsOrth X x0) (hFF : IsFundSet X x0 FF)
    (φ : Frame X.Ψ r → ℝ≥0∞) (hφ : Measurable φ)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) :
    ∑' γ : X.Γ, ∫⁻ z in FF, φ (lact γ.1 (cpt X x0 z)) ∂muF X x0 = ∫⁻ z, φ (cpt X x0 z) ∂muF X x0 := by
  classical
  rw [tsum_congr fun γ : X.Γ => lunfold_one D FF hM hx0 hFF φ hφ hB γ.2]
  rw [← lintegral_tsum]
  swap
  · intro γ
    exact (((measurable_one.indicator (measurableSet_T D FF hFF.1)).comp
      ((measurable_lact γ.1⁻¹).comp (continuous_cpt_apply x0).measurable)).mul
      (hφ.comp (continuous_cpt_apply x0).measurable)).aemeasurable
  apply lintegral_congr_ae
  filter_upwards [ae_mem_omF x0, hFF.2.2.2] with z hz hcov
  obtain ⟨z', hz'F, γ0, hγ0, b0, hb0, hx⟩ := hcov
  have hx' : lact γ0⁻¹ (cpt X x0 z) = rmul (cpt X x0 z') b0 := by rw [hx, lact_inv_apply_lact]
  have hz'O : z' ∈ OmF X x0 := hFF.2.1 hz'F
  obtain ⟨hΔ', hzz', -⟩ := D.uniq z' hz'O b0 hb0
  have hxT : lact γ0⁻¹ (cpt X x0 z) ∈ T D FF := by
    rw [hx']
    show _ ∧ _ ∧ _
    refine ⟨rmul_mem_dom_of_mem_dom hb0 hz'O, hΔ', ?_⟩
    rw [hzz']
    exact hz'F
  have hsum : ∑' γ : X.Γ, (T D FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ.1⁻¹ (cpt X x0 z)) = 1 := by
    rw [tsum_eq_single ⟨γ0, hγ0⟩]
    · exact Set.indicator_of_mem hxT 1
    · intro γ hne
      have hnT : lact γ.1⁻¹ (cpt X x0 z) ∉ T D FF := fun hγT =>
        hne (Subtype.ext (eq_of_lact_inv_cpt_mem_T D FF hFF hz γ.2 hγ0 hγT hxT))
      first
        | exact Set.indicator_of_notMem hnT 1
        | exact Set.indicator_of_not_mem hnT 1
  show ∑' γ : X.Γ, (T D FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ.1⁻¹ (cpt X x0 z)) *
    φ (cpt X x0 z) = φ (cpt X x0 z)
  rw [ENNReal.tsum_mul_right, hsum, one_mul]
end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
