-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_locDens_piece
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:46.31756+00:00
-- url     : https://prove2.me/submissions/f6e45d05-59cb-4ee2-9842-81e62d1bac73

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_hessC_congr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
private lemma maDens_congr_of_hessC_eq {D : ℕ} {F F' : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ k, hessC (F k) y = hessC (F' k) y) : maDens F y = maDens F' y := by
  unfold maDens
  simp only [h]
private lemma two_le_infty_withTop : (2 : WithTop ℕ∞) ≤ ∞ := by
  first
    | exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
    | exact_mod_cast le_top
    | simp
private lemma contDiffAt_two_re_of_analyticAt {D : ℕ} {K : (Fin D → ℂ) → ℂ} {z : Fin D → ℂ}
    (hK : AnalyticAt ℂ K z) : ContDiffAt ℝ 2 (fun w => (K w).re) z :=
  Complex.reCLM.contDiff.contDiffAt.comp z (hK.contDiffAt.restrict_scalars ℝ)
private lemma hessC_add_potential {D : ℕ} {f g : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (hf : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2 f z) (hg : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2 g z) :
    hessC (fun z => f z + g z) y = hessC f y + hessC g y := by
  have hd : fderiv ℝ (fun z => f z + g z) =ᶠ[𝓝 y] fun z => fderiv ℝ f z + fderiv ℝ g z := by
    filter_upwards [hf, hg] with z h1 h2
    exact fderiv_add (h1.differentiableAt (by first | norm_num | exact one_le_two | simp))
      (h2.differentiableAt (by first | norm_num | exact one_le_two | simp))
  have hf2 : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hf.self_of_nhds.fderiv_right (m := 1)
      (by first | norm_num | exact le_of_eq one_add_one_eq_two | simp)).differentiableAt (by first | exact one_ne_zero | norm_num | simp)
  have hg2 : DifferentiableAt ℝ (fderiv ℝ g) y :=
    (hg.self_of_nhds.fderiv_right (m := 1)
      (by first | norm_num | exact le_of_eq one_add_one_eq_two | simp)).differentiableAt (by first | exact one_ne_zero | norm_num | simp)
  have hH : fderiv ℝ (fderiv ℝ (fun z => f z + g z)) y =
      fderiv ℝ (fderiv ℝ f) y + fderiv ℝ (fderiv ℝ g) y := by
    rw [hd.fderiv_eq]
    exact fderiv_add hf2 hg2
  ext i k
  simp only [hessC, hH, Matrix.add_apply, ContinuousLinearMap.add_apply]
  push_cast
  ring
private lemma hessC_re_of_analyticAt {D : ℕ} {H : (Fin D → ℂ) → ℂ} {y : Fin D → ℂ}
    (hH : AnalyticAt ℂ H y) : hessC (fun z => (H z).re) y = 0 := by
  have h1 : fderiv ℝ (fun z => (H z).re) =ᶠ[𝓝 y] fun z =>
      (ContinuousLinearMap.compL ℝ (Fin D → ℂ) ℂ ℝ Complex.reCLM)
        ((ContinuousLinearMap.restrictScalarsL ℂ (Fin D → ℂ) ℂ ℝ ℝ) (fderiv ℂ H z)) := by
    filter_upwards [hH.eventually_analyticAt] with z hz
    have hd : HasFDerivAt (fun w => (H w).re)
        (Complex.reCLM.comp ((fderiv ℂ H z).restrictScalars ℝ)) z :=
      Complex.reCLM.hasFDerivAt.comp z (hz.differentiableAt.hasFDerivAt.restrictScalars ℝ)
    rw [hd.fderiv]
    first
      | rfl
      | (ext v; simp)
  have hD : HasFDerivAt (fderiv ℂ H) ((fderiv ℂ (fderiv ℂ H) y).restrictScalars ℝ) y :=
    hH.fderiv.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have h2 : HasFDerivAt (fun z => (ContinuousLinearMap.compL ℝ (Fin D → ℂ) ℂ ℝ Complex.reCLM)
        ((ContinuousLinearMap.restrictScalarsL ℂ (Fin D → ℂ) ℂ ℝ ℝ) (fderiv ℂ H z)))
      ((ContinuousLinearMap.compL ℝ (Fin D → ℂ) ℂ ℝ Complex.reCLM).comp
        ((ContinuousLinearMap.restrictScalarsL ℂ (Fin D → ℂ) ℂ ℝ ℝ).comp
          ((fderiv ℂ (fderiv ℂ H) y).restrictScalars ℝ))) y :=
    (ContinuousLinearMap.compL ℝ (Fin D → ℂ) ℂ ℝ Complex.reCLM).hasFDerivAt.comp y
    ((ContinuousLinearMap.restrictScalarsL ℂ (Fin D → ℂ) ℂ ℝ ℝ).hasFDerivAt.comp y hD)
  have hv : ∀ v w : Fin D → ℂ, fderiv ℝ (fderiv ℝ fun z => (H z).re) y v w =
      (fderiv ℂ (fderiv ℂ H) y v w).re := by
    intro v w
    rw [h1.fderiv_eq, h2.fderiv]
    first
      | rfl
      | simp
  ext i k
  simp only [hessC, hv, Matrix.zero_apply, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp [Complex.mul_re, Complex.mul_im]
section Piece
variable [CompactSpace X] [T2Space X] (A : FinHolAtlas (e + 1) X) (Φ : Fin e → LocPot X)
  (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (G : Set X) (hGo : IsOpen G)
  (hG : G ⊆ (A.chart j).source) (x0 : Fin e → X) (hGU : ∀ i, G ⊆ (Φ i).U (x0 i))
end Piece
end
end ReciprocityTheory.AnForm.M
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
variable [CompactSpace X] [T2Space X] (A : FinHolAtlas (e + 1) X) (Φ : Fin e → LocPot X)
  (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (G : Set X) (hGo : IsOpen G)
  (hG : G ⊆ (A.chart j).source) (x0 : Fin e → X) (hGU : ∀ i, G ⊆ (Φ i).U (x0 i))
include hΦ hG hGU
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (u : X → ℝ) (hu : A.Smooth u) {y : Fin (e + 1) → ℂ}
    (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' G) :
    locDens A (Fin.cons (LocPot.ofFun u) Φ) j y =
      maDens (Fin.cons (u ∘ (A.chart j).symm) fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm) y := by
  unfold locDens
  apply maDens_congr_of_hessC_eq
  intro k
  refine Fin.cases ?_ (fun i => ?_) k
  · first
      | rfl
      | (simp only [Fin.cons_zero]; rfl)
      | simp [LocPot.ofFun, Function.comp_def]
  · simp only [Fin.cons_succ]
    have hyG : (A.chart j).symm y ∈ G := hy.2
    obtain ⟨W, hWo, haW, Gh, hGh, hdiff⟩ :=
      (hΦ i).2 ((A.chart j).symm y) (x0 i) ((A.chart j).symm y) ⟨(Φ i).mem_U _, hGU i hyG⟩
    have hSo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹'
        (W ∩ (Φ i).U ((A.chart j).symm y) ∩ (Φ i).U (x0 i))) :=
      (A.chart j).isOpen_inter_preimage_symm ((hWo.inter ((Φ i).isOpen_U _)).inter ((Φ i).isOpen_U _))
    have hyS : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹'
        (W ∩ (Φ i).U ((A.chart j).symm y) ∩ (Φ i).U (x0 i)) :=
      ⟨hy.1, ⟨⟨haW, (Φ i).mem_U _⟩, hGU i hyG⟩⟩
    have hSn := hSo.mem_nhds hyS
    have hf2 : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2 ((Φ i).φ (x0 i) ∘ (A.chart j).symm) z := by
      filter_upwards [hSn] with z hz
      have hon := (hΦ i).1 (x0 i) j
      exact ((hon.mono (fun w hw => ⟨hw.1, hw.2.2⟩)).contDiffAt (hSo.mem_nhds hz)).of_le
        two_le_infty_withTop
    have hK : ∀ z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹'
        (W ∩ (Φ i).U ((A.chart j).symm y) ∩ (Φ i).U (x0 i)),
        AnalyticAt ℂ (Gh ∘ (A.chart j).symm) z := fun z hz => hGh j z ⟨hz.1, hz.2.1.1⟩
    have hh : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2 (fun w => ((Gh ∘ (A.chart j).symm) w).re) z := by
      filter_upwards [hSn] with z hz
      exact contDiffAt_two_re_of_analyticAt (hK z hz)
    have heq : (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[𝓝 y]
        fun w => ((Φ i).φ (x0 i) ∘ (A.chart j).symm) w + ((Gh ∘ (A.chart j).symm) w).re := by
      filter_upwards [hSn] with z hz
      have hz' := hdiff ((A.chart j).symm z) hz.2
      simp only [Function.comp_apply]
      linarith
    rw [st_hessC_congr heq, hessC_add_potential hf2 hh, hessC_re_of_analyticAt (hK y hyS), add_zero]
end ReciprocityTheory.AnForm.M
