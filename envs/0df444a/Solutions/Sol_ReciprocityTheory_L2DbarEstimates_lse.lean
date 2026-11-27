-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.lse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:42:30.921861+00:00
-- url     : https://prove2.me/submissions/76e8d757-0a06-4d27-b236-7f6e87ff3870

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_LseSmoothRIffReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_lse_two_le_infty
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_lse_smoothR_iff_real
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_holo_contDiffOn_complex
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_lseV
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates
open Filter Topology
open scoped ContDiff
private theorem chart_symm_apply_eventually_eq {M : Type*} [TopologicalSpace M] {n : ℕ} {z : M → V n}
    (hz : IsLocalHomeomorph z) {e e' : OpenPartialHomeomorph M (V n)} (he : IsChart n z e)
    (he' : IsChart n z e') {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    ∀ᶠ w in 𝓝 (z x), e.symm w = e'.symm w := by
  obtain ⟨f, hxf, hzf⟩ := hz x
  have hzx : z x = e x := he hx
  have hzx' : z x = e' x := he' hx'
  have h1 : ∀ᶠ w in 𝓝 (z x), e.symm w ∈ f.source := by
    rw [hzx]
    exact (e.continuousAt_symm (e.map_source hx)).preimage_mem_nhds
      (by rw [e.left_inv hx]; exact f.open_source.mem_nhds hxf)
  have h2 : ∀ᶠ w in 𝓝 (z x), e'.symm w ∈ f.source := by
    rw [hzx']
    exact (e'.continuousAt_symm (e'.map_source hx')).preimage_mem_nhds
      (by rw [e'.left_inv hx']; exact f.open_source.mem_nhds hxf)
  have h3 : ∀ᶠ w in 𝓝 (z x), w ∈ e.target := by
    rw [hzx]
    exact e.open_target.mem_nhds (e.map_source hx)
  have h4 : ∀ᶠ w in 𝓝 (z x), w ∈ e'.target := by
    rw [hzx']
    exact e'.open_target.mem_nhds (e'.map_source hx')
  filter_upwards [h1, h2, h3, h4] with w hw1 hw2 hw3 hw4
  have k1 : f (e.symm w) = w := by rw [← hzf, he (e.map_target hw3), e.right_inv hw3]
  have k2 : f (e'.symm w) = w := by rw [← hzf, he' (e'.map_target hw4), e'.right_inv hw4]
  calc e.symm w = f.symm (f (e.symm w)) := (f.left_inv hw1).symm
    _ = f.symm (f (e'.symm w)) := by rw [k1, k2]
    _ = e'.symm w := f.left_inv hw2
private theorem d_eq_wd_of_isLocalHomeomorph_chart {M : Type*} [TopologicalSpace M] {n : ℕ} {z : M → V n}
    (hz : IsLocalHomeomorph z) {e : OpenPartialHomeomorph M (V n)} (he : IsChart n z e)
    {x : M} (hx : x ∈ e.source) (j : Fin n) (g : M → ℂ) :
    d n z j g x = wd n j (g ∘ e.symm) (z x) := by
  have h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := ⟨e, he, hx⟩
  unfold d
  rw [dif_pos h]
  apply wd_congr
  filter_upwards [chart_symm_apply_eventually_eq hz (Classical.choose_spec h).1 he (Classical.choose_spec h).2 hx]
    with w hw
  simp only [Function.comp_apply, hw]
private theorem db_eq_wdb_of_isLocalHomeomorph_chart {M : Type*} [TopologicalSpace M] {n : ℕ} {z : M → V n}
    (hz : IsLocalHomeomorph z) {e : OpenPartialHomeomorph M (V n)} (he : IsChart n z e)
    {x : M} (hx : x ∈ e.source) (j : Fin n) (g : M → ℂ) :
    db n z j g x = wdb n j (g ∘ e.symm) (z x) := by
  have h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := ⟨e, he, hx⟩
  unfold db
  rw [dif_pos h]
  apply wdb_congr
  filter_upwards [chart_symm_apply_eventually_eq hz (Classical.choose_spec h).1 he (Classical.choose_spec h).2 hx]
    with w hw
  simp only [Function.comp_apply, hw]
private theorem levi_eq_leviV_comp_chart_symm {M : Type*} [TopologicalSpace M] {n : ℕ} {z : M → V n}
    (hz : IsLocalHomeomorph z) {e : OpenPartialHomeomorph M (V n)} (he : IsChart n z e)
    {x : M} (hx : x ∈ e.source) (ph : M → ℝ) (ξ : Fin n → ℂ) :
    Levi n z ph x ξ = leviV n (fun y => ((ph (e.symm y) : ℝ) : ℂ)) (z x) ξ := by
  unfold Levi leviV
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  have hzx : z x = e x := he hx
  have hnh : ∀ᶠ w in 𝓝 (z x), w ∈ e.target := by
    rw [hzx]
    exact e.open_target.mem_nhds (e.map_source hx)
  have hev : (db n z k fun y => (ph y : ℂ)) ∘ e.symm =ᶠ[𝓝 (z x)]
      wdb n k (fun y => ((ph (e.symm y) : ℝ) : ℂ)) := by
    filter_upwards [hnh] with w hw
    rw [Function.comp_apply, db_eq_wdb_of_isLocalHomeomorph_chart hz he (e.map_target hw) k, he (e.map_target hw),
      e.right_inv hw]
    try rfl
  rw [d_eq_wd_of_isLocalHomeomorph_chart hz he hx, wd_congr hev]
end ReciprocityTheory.L2DbarEstimates
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open Filter Topology
open scoped ContDiff
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] : LSEStatement n M := by
  intro z hz p q ph g hph hL hg hpos
  have hchart : ∀ x : M, ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := by
    intro x
    obtain ⟨f, hxf, hzf⟩ := hz x
    exact ⟨f, fun y _ => by rw [hzf], hxf⟩
  have hsm : ∀ e : OpenPartialHomeomorph M (V n), IsChart n z e →
      ContDiffOn ℝ ∞ (fun v => Real.log (∑ i, Real.exp (ph i (e.symm v)) +
        ∑ j, ‖g j (e.symm v)‖ ^ 2)) e.target := by
    intro e he
    have h1 : ∀ i, ContDiffOn ℝ ∞ (fun v => ph i (e.symm v)) e.target :=
      fun i => (lse_smoothR_iff_real n z (ph i)).mp (hph i) e he
    have h2 : ∀ j, ContDiffOn ℝ ∞ (fun v => g j (e.symm v)) e.target :=
      fun j => by
        have hgd : DifferentiableOn ℂ (fun v => g j (e.symm v)) e.target := hg j e he
        have hgc : ContDiffOn ℂ ∞ (fun v => g j (e.symm v)) e.target := by
          exact C.holo_contDiffOn_complex e.open_target hgd
        exact hgc.restrict_scalars ℝ
    refine ContDiffOn.log ?_ fun v _ => (hpos (e.symm v)).ne'
    exact (ContDiffOn.sum fun i _ => (h1 i).exp).add (ContDiffOn.sum fun j _ => (h2 j).norm_sq ℝ)
  refine ⟨(lse_smoothR_iff_real n z _).mpr fun e he => hsm e he, fun x ξ => ?_⟩
  obtain ⟨e, he, hx⟩ := hchart x
  rw [levi_eq_leviV_comp_chart_symm hz he hx]
  set u : Fin (p + q) → V n → ℝ := fun i => Fin.addCases (fun i y => Real.exp (ph i (e.symm y)))
      (fun j y => ‖g j (e.symm y)‖ ^ 2) i with hu
  have hsum : ∀ y, ∑ i, u i y = ∑ i, Real.exp (ph i (e.symm y)) + ∑ j, ‖g j (e.symm y)‖ ^ 2 := by
    intro y
    rw [Fin.sum_univ_add]
    simp [hu]
  have hzx : z x = e x := he hx
  have hmem : z x ∈ e.target := by
    rw [hzx]
    exact e.map_source hx
  have hA : ∀ i, (∃ φ : V n → ℝ, ContDiffOn ℝ 2 φ e.target ∧ LeviNonnegOn n φ e.target ∧
        ∀ y ∈ e.target, u i y = Real.exp (φ y)) ∨
      (∃ g' : V n → ℂ, ContDiffOn ℂ 2 g' e.target ∧
        ∀ y ∈ e.target, u i y = Complex.normSq (g' y)) := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      left
      refine ⟨fun y => ph i (e.symm y),
        ((lse_smoothR_iff_real n z (ph i)).mp (hph i) e he).of_le lse_two_le_infty, ?_,
        fun y _ => by simp [hu]⟩
      intro y hy ζ
      have h := hL i (e.symm y) ζ
      rw [levi_eq_leviV_comp_chart_symm hz he (e.map_target hy), he (e.map_target hy), e.right_inv hy] at h
      exact h
    | right j =>
      right
      have hgd : DifferentiableOn ℂ (fun v => g j (e.symm v)) e.target := hg j e he
      have hgc : ContDiffOn ℂ 2 (fun v => g j (e.symm v)) e.target :=
        (C.holo_contDiffOn_complex e.open_target hgd).of_le (by
          first
          | exact WithTop.coe_le_coe.mpr le_top
          | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
          | simp)
      refine ⟨fun y => g j (e.symm y), hgc, fun y _ => ?_⟩
      simp [hu, Complex.normSq_eq_norm_sq]
  have hB : ∀ y ∈ e.target, 0 < ∑ i, u i y := by
    intro y _
    rw [hsum]
    exact hpos (e.symm y)
  have key := lseV n (p + q) e.target u e.open_target hA hB (z x) hmem ξ
  have e1 : leviV n (fun y => ((Real.log (∑ i, u i y) : ℝ) : ℂ)) (z x) ξ =
      leviV n (fun y => ((Real.log (∑ i, Real.exp (ph i (e.symm y)) +
        ∑ j, ‖g j (e.symm y)‖ ^ 2) : ℝ) : ℂ)) (z x) ξ := by
    congr 1
    funext y
    rw [hsum]
  rw [e1] at key
  exact key
end ReciprocityTheory.L2DbarEstimates
