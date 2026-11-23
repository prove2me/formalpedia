-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.lunfold_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:53:38.503267+00:00
-- url     : https://prove2.me/submissions/ae7674b5-4e92-4cd9-8a4e-16d9cc7caeb5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_ind_rmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_ind_cpt
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
private theorem cpt_lact_upper_bounds (γ : GL (Fin r) E) (y0 : Frame X.Ψ r) (z : V (nd X)) :
    cpt X (lact γ y0) z = lact γ (cpt X y0 z) := by
  show rmul (lact γ y0) (nmat X z) = lact γ (rmul y0 (nmat X z))
  funext τ
  dsimp only [lact, rmul, mat]
  exact Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (Matrix.of (y0 τ))
    (Matrix.of (nmat X z τ))
private theorem gram_mat_lact_of_mem_Γ {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat (lact γ x) τ) =
      ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) := by
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
  rw [hmat, gram_eq_lemma, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rw [hU']
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
private theorem muF_lact_upper_bounds {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (y0 : Frame X.Ψ r) :
    muF X (lact γ y0) = muF X y0 := by
  have hOm : OmF X (lact γ y0) = OmF X y0 := by
    ext z
    show cpt X (lact γ y0) z ∈ X.dom ↔ cpt X y0 z ∈ X.dom
    rw [cpt_lact_upper_bounds]
    constructor
    · intro h
      have h2 := lact_mem_dom' (X.Γ.inv_mem hγ) h
      rwa [lact_inv_apply_lact] at h2
    · intro h
      exact lact_mem_dom' hγ h
  have hd : ∀ z, ReciprocityTheory.ChartRestriction.G.AR.Up.densF X (lact γ y0) z = ReciprocityTheory.ChartRestriction.G.AR.Up.densF X y0 z := by
    intro z
    unfold ReciprocityTheory.ChartRestriction.G.AR.Up.densF
    rw [cpt_lact_upper_bounds]
    simp only [ReciprocityTheory.ChartRestriction.G.FD.dmin, gram_mat_lact_of_mem_Γ hγ]
  unfold ReciprocityTheory.ChartRestriction.G.AR.Up.muF
  rw [hOm]
  simp only [hd]
private theorem isOrth_lact' {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {y0 : Frame X.Ψ r} (h : IsOrth X y0) :
    IsOrth X (lact γ y0) := by
  intro τ
  rw [gram_mat_lact_of_mem_Γ hγ]
  exact h τ
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
theorem _root_.solution (hM : MeasInvStatement (E := E)) (hx0 : IsOrth X x0) (hFF : IsFundSet X x0 FF)
    (φ : Frame X.Ψ r → ℝ≥0∞) (hφ : Measurable φ)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    ∫⁻ z in FF, φ (lact γ (cpt X x0 z)) ∂muF X x0 =
      ∫⁻ z, (T D FF).indicator 1 (lact γ⁻¹ (cpt X x0 z)) * φ (cpt X x0 z) ∂muF X x0 := by
  classical
  obtain ⟨Fn, hFn⟩ : ∃ Fn : Frame X.Ψ r → ℝ≥0∞,
      Fn = fun x => (T D FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ⁻¹ x) * φ x := ⟨_, rfl⟩
  have hFm : Measurable Fn := by
    rw [hFn]
    exact ((measurable_one.indicator (measurableSet_T D FF hFF.1)).comp (measurable_lact γ⁻¹)).mul hφ
  have hFB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Fn (rmul x b) = Fn x := by
    intro x hx b hb
    rw [hFn]
    simp only [ind_rmul D FF hγ hx hb (M := ℝ≥0∞), hB x hx b hb]
  have hpt : ∀ z ∈ OmF X x0,
      FF.indicator (fun z => φ (lact γ (cpt X x0 z))) z = Fn (lact γ (cpt X x0 z)) := by
    intro z hz
    rw [hFn]
    dsimp only
    rw [lact_inv_apply_lact, ind_cpt D FF hz (M := ℝ≥0∞)]
    by_cases h : z ∈ FF
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply, one_mul]
    · first
        | rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
        | rw [Set.indicator_of_not_mem h, Set.indicator_of_not_mem h, zero_mul]
  rw [← lintegral_indicator hFF.1]
  calc ∫⁻ z, FF.indicator (fun z => φ (lact γ (cpt X x0 z))) z ∂muF X x0
      = ∫⁻ z, Fn (lact γ (cpt X x0 z)) ∂muF X x0 :=
        lintegral_congr_ae ((ae_mem_omF x0).mono fun z hz => hpt z hz)
    _ = ∫⁻ z, Fn (cpt X (lact γ x0) z) ∂muF X (lact γ x0) := by
        rw [muF_lact_upper_bounds hγ]
        simp only [cpt_lact_upper_bounds]
    _ = ∫⁻ z, Fn (cpt X x0 z) ∂muF X x0 :=
        hM r X (lact γ x0) x0 (isOrth_lact' hγ hx0) hx0 Fn hFm hFB
    _ = _ := by rw [hFn]
end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
