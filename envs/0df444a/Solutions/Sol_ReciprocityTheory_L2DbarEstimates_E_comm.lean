-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.E.comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:02:49.233184+00:00
-- url     : https://prove2.me/submissions/1edffc79-ff98-4bd5-bf76-7324a14cbb9e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_ImportsBis
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.E
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
private lemma chart_symm_eventuallyEq_of_isChart {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (he' : IsChart n z e')
    (p : M) (hp : p ∈ e.source) (hp' : p ∈ e'.source) :
    e.symm =ᶠ[nhds (z p)] e'.symm := by
  have he0 : Set.EqOn z e e.source := he
  have he0' : Set.EqOn z e' e'.source := he'
  have hzp : z p = e' p := he0' hp'
  have h2 : e'.target ∩ e'.symm ⁻¹' e.source ∈ nhds (z p) := by
    rw [hzp]
    refine (e'.isOpen_inter_preimage_symm e.open_source).mem_nhds ⟨e'.map_source hp', ?_⟩
    rw [Set.mem_preimage, e'.left_inv hp']
    exact hp
  filter_upwards [h2] with y hy
  have hs : e'.symm y ∈ e'.source := e'.map_target hy.1
  have h3 : e (e'.symm y) = y := by
    rw [← he0 hy.2, he0' hs, e'.right_inv hy.1]
  calc e.symm y = e.symm (e (e'.symm y)) := by rw [h3]
    _ = e'.symm y := e.left_inv hy.2
private lemma db_eq_wdb_comp_chart_symm {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e0 : OpenPartialHomeomorph M (V n)) (he0 : IsChart n z e0) (k : Fin n) (g : M → ℂ)
    (p : M) (hp : p ∈ e0.source) : db n z k g p = wdb n k (g ∘ e0.symm) (z p) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ p ∈ e.source := ⟨e0, he0, hp⟩
  have hspec := Classical.choose_spec hex
  have hE : (g ∘ (Classical.choose hex).symm) =ᶠ[nhds (z p)] (g ∘ e0.symm) :=
    (chart_symm_eventuallyEq_of_isChart z _ e0 hspec.1 he0 p hspec.2 hp).fun_comp g
  rw [db, dif_pos hex]
  unfold wdb
  rw [hE.fderiv_eq]
private lemma d_apply_eq_wd_of_mem_source {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e0 : OpenPartialHomeomorph M (V n)) (he0 : IsChart n z e0) (k : Fin n) (g : M → ℂ)
    (p : M) (hp : p ∈ e0.source) : d n z k g p = wd n k (g ∘ e0.symm) (z p) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ p ∈ e.source := ⟨e0, he0, hp⟩
  have hspec := Classical.choose_spec hex
  have hE : (g ∘ (Classical.choose hex).symm) =ᶠ[nhds (z p)] (g ∘ e0.symm) :=
    (chart_symm_eventuallyEq_of_isChart z _ e0 hspec.1 he0 p hspec.2 hp).fun_comp g
  rw [d, dif_pos hex]
  unfold wd
  rw [hE.fderiv_eq]
private lemma differentiableAt_wdb_and_fderiv_wdb_eq {n : ℕ} (k : Fin n) (h : V n → ℂ) (y0 : V n)
    (hd : DifferentiableAt ℝ (fderiv ℝ h) y0) :
    DifferentiableAt ℝ (wdb n k h) y0 ∧ ∀ v : V n, fderiv ℝ (wdb n k h) y0 v =
      (fderiv ℝ (fderiv ℝ h) y0 v (bas n k) +
        Complex.I * fderiv ℝ (fderiv ℝ h) y0 v (Complex.I • bas n k)) / 2 := by
  have hA := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (bas n k) y0)
  have hB := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Complex.I • bas n k) y0)
  have hW := HasFDerivAt.const_mul (HasFDerivAt.add hA (HasFDerivAt.const_mul hB Complex.I))
    ((2 : ℂ)⁻¹)
  have heq : wdb n k h = fun y =>
      (2 : ℂ)⁻¹ * (fderiv ℝ h y (bas n k) + Complex.I * fderiv ℝ h y (Complex.I • bas n k)) := by
    funext y
    rw [wdb, div_eq_inv_mul]
  have hW' : HasFDerivAt (wdb n k h) ((2 : ℂ)⁻¹ •
      ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) + (fderiv ℝ (fderiv ℝ h) y0).flip (bas n k) +
        Complex.I • ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) +
          (fderiv ℝ (fderiv ℝ h) y0).flip (Complex.I • bas n k)))) y0 := by
    rw [heq]
    exact hW
  refine ⟨HasFDerivAt.differentiableAt hW', fun v => ?_⟩
  rw [HasFDerivAt.fderiv hW']
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply, smul_eq_mul]
  ring
private lemma differentiableAt_wd_and_fderiv_wd_eq {n : ℕ} (k : Fin n) (h : V n → ℂ) (y0 : V n)
    (hd : DifferentiableAt ℝ (fderiv ℝ h) y0) :
    DifferentiableAt ℝ (wd n k h) y0 ∧ ∀ v : V n, fderiv ℝ (wd n k h) y0 v =
      (fderiv ℝ (fderiv ℝ h) y0 v (bas n k) -
        Complex.I * fderiv ℝ (fderiv ℝ h) y0 v (Complex.I • bas n k)) / 2 := by
  have hA := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (bas n k) y0)
  have hB := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Complex.I • bas n k) y0)
  have hW := HasFDerivAt.const_mul (HasFDerivAt.sub hA (HasFDerivAt.const_mul hB Complex.I))
    ((2 : ℂ)⁻¹)
  have heq : wd n k h = fun y =>
      (2 : ℂ)⁻¹ * (fderiv ℝ h y (bas n k) - Complex.I * fderiv ℝ h y (Complex.I • bas n k)) := by
    funext y
    rw [wd, div_eq_inv_mul]
  have hW' : HasFDerivAt (wd n k h) ((2 : ℂ)⁻¹ •
      ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) + (fderiv ℝ (fderiv ℝ h) y0).flip (bas n k) -
        Complex.I • ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) +
          (fderiv ℝ (fderiv ℝ h) y0).flip (Complex.I • bas n k)))) y0 := by
    rw [heq]
    exact hW
  refine ⟨HasFDerivAt.differentiableAt hW', fun v => ?_⟩
  rw [HasFDerivAt.fderiv hW']
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply,
    smul_eq_mul]
  ring
end
end ReciprocityTheory.L2DbarEstimates.E
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.E
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.E
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] : CommStatement n M := by
  intro z hz ph j k u x hph hu
  obtain ⟨e0, hx0, hze⟩ := hz x
  have he0 : IsChart n z e0 := by
    intro y _
    rw [hze]
  have he0' : Set.EqOn z e0 e0.source := he0
  have hy0 : z x ∈ e0.target := by
    rw [he0' hx0]
    exact e0.map_source hx0
  have hnb : e0.target ∈ nhds (z x) := e0.open_target.mem_nhds hy0
  have hcH : ContDiffAt ℝ 2 (u ∘ e0.symm) (z x) := by
    have := (hu e0 he0).contDiffAt hnb
    simpa using this
  have hcP : ContDiffAt ℝ 2 ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) (z x) := by
    have := (hph e0 he0).contDiffAt hnb
    simpa using this
  have hdH : DifferentiableAt ℝ (fderiv ℝ (u ∘ e0.symm)) (z x) :=
    (hcH.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdP : DifferentiableAt ℝ (fderiv ℝ ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm)) (z x) :=
    (hcP.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hH : DifferentiableAt ℝ (u ∘ e0.symm) (z x) := hcH.differentiableAt (by norm_num)
  have hsymH : ∀ v w : V n, fderiv ℝ (fderiv ℝ (u ∘ e0.symm)) (z x) v w =
      fderiv ℝ (fderiv ℝ (u ∘ e0.symm)) (z x) w v := by
    intro v w
    first
      | exact hcH.isSymmSndFDerivAt (by simp) v w
      | exact hcH.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) v w
  have hsymP : ∀ v w : V n, fderiv ℝ (fderiv ℝ ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm)) (z x) v w =
      fderiv ℝ (fderiv ℝ ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm)) (z x) w v := by
    intro v w
    first
      | exact hcP.isSymmSndFDerivAt (by simp) v w
      | exact hcP.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) v w
  have hloc1 : ((db n z j u) ∘ e0.symm) =ᶠ[nhds (z x)] wdb n j (u ∘ e0.symm) := by
    filter_upwards [hnb] with y hy
    rw [Function.comp_apply, db_eq_wdb_comp_chart_symm z e0 he0 j u _ (e0.map_target hy),
      he0' (e0.map_target hy), e0.right_inv hy]
  have hloc2 : ((db n z j (fun y => ((ph y : ℝ) : ℂ))) ∘ e0.symm) =ᶠ[nhds (z x)] wdb n j ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) := by
    filter_upwards [hnb] with y hy
    rw [Function.comp_apply, db_eq_wdb_comp_chart_symm z e0 he0 j _ _ (e0.map_target hy),
      he0' (e0.map_target hy), e0.right_inv hy]
  have hloc3 : ((fun y => d n z k u y - u y * d n z k (fun y => ((ph y : ℝ) : ℂ)) y) ∘ e0.symm) =ᶠ[nhds (z x)]
      (fun y => wd n k (u ∘ e0.symm) y - (u ∘ e0.symm) y * wd n k ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) y) := by
    filter_upwards [hnb] with y hy
    have hp := e0.map_target hy
    rw [Function.comp_apply, d_apply_eq_wd_of_mem_source z e0 he0 k u _ hp, d_apply_eq_wd_of_mem_source z e0 he0 k _ _ hp,
      he0' hp, e0.right_inv hy]
    rfl
  have hux : u x = (u ∘ e0.symm) (z x) := by
    rw [Function.comp_apply, he0' hx0, e0.left_inv hx0]
  have hW1 := (differentiableAt_wdb_and_fderiv_wdb_eq j _ _ hdH).2
  have hW2 := differentiableAt_wd_and_fderiv_wd_eq k _ _ hdH
  have hW3 := differentiableAt_wd_and_fderiv_wd_eq k _ _ hdP
  have hW4 := (differentiableAt_wdb_and_fderiv_wdb_eq j _ _ hdP).2
  have hFG : fderiv ℝ (fun y => wd n k (u ∘ e0.symm) y - (u ∘ e0.symm) y * wd n k ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) y) (z x) =
      fderiv ℝ (wd n k (u ∘ e0.symm)) (z x) - ((u ∘ e0.symm) (z x) • fderiv ℝ (wd n k ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm)) (z x) +
        wd n k ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) (z x) • fderiv ℝ (u ∘ e0.symm) (z x)) := by
    have h1 := HasFDerivAt.sub (DifferentiableAt.hasFDerivAt hW2.1)
      (HasFDerivAt.mul (DifferentiableAt.hasFDerivAt hH) (DifferentiableAt.hasFDerivAt hW3.1))
    exact HasFDerivAt.fderiv h1
  show (d n z k (db n z j u) x - db n z j u x * d n z k (fun y => ((ph y : ℝ) : ℂ)) x) -
      db n z j (fun y => d n z k u y - u y * d n z k (fun y => ((ph y : ℝ) : ℂ)) y) x =
    d n z k (db n z j (fun y => ((ph y : ℝ) : ℂ))) x * u x
  rw [d_apply_eq_wd_of_mem_source z e0 he0 k (db n z j u) x hx0, db_eq_wdb_comp_chart_symm z e0 he0 j u x hx0,
    d_apply_eq_wd_of_mem_source z e0 he0 k (fun y => ((ph y : ℝ) : ℂ)) x hx0, db_eq_wdb_comp_chart_symm z e0 he0 j _ x hx0,
    d_apply_eq_wd_of_mem_source z e0 he0 k (db n z j (fun y => ((ph y : ℝ) : ℂ))) x hx0, hux]
  unfold wd wdb
  rw [hloc1.fderiv_eq, hloc2.fderiv_eq, hloc3.fderiv_eq, hFG]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hW1 (bas n k), hW1 (Complex.I • bas n k), hW2.2 (bas n j), hW2.2 (Complex.I • bas n j),
    hW3.2 (bas n j), hW3.2 (Complex.I • bas n j), hW4 (bas n k), hW4 (Complex.I • bas n k)]
  unfold wd
  rw [hsymH (bas n k) (bas n j), hsymH (bas n k) (Complex.I • bas n j),
    hsymH (Complex.I • bas n k) (bas n j), hsymH (Complex.I • bas n k) (Complex.I • bas n j),
    hsymP (bas n k) (bas n j), hsymP (bas n k) (Complex.I • bas n j),
    hsymP (Complex.I • bas n k) (bas n j), hsymP (Complex.I • bas n k) (Complex.I • bas n j)]
  ring
end ReciprocityTheory.L2DbarEstimates.E
