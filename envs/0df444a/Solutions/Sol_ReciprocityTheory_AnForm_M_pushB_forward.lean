-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.pushB_forward
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:24:04.915292+00:00
-- url     : https://prove2.me/submissions/ad60c738-b767-4fb0-b385-45b06d94e61d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushBForward
import Theorems.Thm_ReciprocityTheory_AnForm_M_analyticNull
import Theorems.Thm_ReciprocityTheory_AnForm_M_existsPartition
import Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_analytic
import Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_cover
import Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_dens
import Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_finsum_inter
import Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_hasSum_ind
import Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_intOn
import Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_intTsum
import Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_isClosed
import Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_locInj
import Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_piece
import Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_piece_norm
import Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_sum_finsum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : PushForwardStatement := by
  intro e X _ _ _ A Φ hΦ q T S hT hTS hS hint hq hdet hfin g hg
  have hne := existsPartition A
  rw [mInt, dif_pos hne]
  set P := hne.some with hP
  have hSc : IsClosed S := pushA_isClosed A hS
  have hTc : ∀ x, x ∉ S → x ∈ Tᶜ := fun x hx hxT => hx (hTS hxT)
  set h : Fin A.n → X → ℝ := fun j x => P.χ j x * g x * pushDens A Φ q x with hh
  have hO : ∀ j, IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Sᶜ) :=
    fun j => (A.chart j).isOpen_inter_preimage_symm hSc.isOpen_compl
  have hloc : ∀ j, ∀ z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Sᶜ, ∃ W : Set (Fin e → ℂ),
      IsOpen W ∧ z ∈ W ∧ Set.InjOn (q ∘ (A.chart j).symm) W := by
    intro j z hz
    apply pushA_locInj (pushA_analytic A hq j hz.1 (hTc _ hz.2))
    have := hdet _ hz.2 j ((A.chart j).map_target hz.1)
    rwa [(A.chart j).right_inv hz.1] at this
  choose D hDm hDd hDU hDi using fun j => pushA_cover _ (hO j) _ (hloc j)
  have hDO : ∀ j m, D j m ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Sᶜ := by
    intro j m z hz
    rw [← hDU j]
    exact Set.mem_iUnion.2 ⟨m, hz⟩

  have hEq : ∀ j, Set.EqOn (fun z => Complex.normSq (LinearMap.det
        (fderiv ℂ (q ∘ (A.chart j).symm) z : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) *
        h j ((A.chart j).symm z))
      (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Sᶜ) := by
    intro j z hz
    have hd := pushA_dens A Φ hΦ hq j hz.1 (hTc _ hz.2)
      (hdet _ hz.2 (chartIdx A _) (Classical.choose_spec (A.cover _)))
    simp only [hh]
    rw [← hd]
    ring
  have hEqN : ∀ j, Set.EqOn (fun z => Complex.normSq (LinearMap.det
        (fderiv ℂ (q ∘ (A.chart j).symm) z : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) *
        |h j ((A.chart j).symm z)|)
      (fun y => ‖P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y‖)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Sᶜ) := by
    intro j z hz
    have h1 : Complex.normSq (LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) z :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) * h j ((A.chart j).symm z) =
        P.χ j ((A.chart j).symm z) * g ((A.chart j).symm z) * locDens A Φ j z := hEq j hz
    show Complex.normSq (LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) z :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) * |h j ((A.chart j).symm z)| =
      ‖P.χ j ((A.chart j).symm z) * g ((A.chart j).symm z) * locDens A Φ j z‖
    rw [← h1, Real.norm_eq_abs, abs_mul (Complex.normSq _) (h j ((A.chart j).symm z)),
      abs_of_nonneg (Complex.normSq_nonneg _)]
  have hdiff : ∀ j m, ∀ z ∈ D j m, DifferentiableAt ℂ (q ∘ (A.chart j).symm) z := fun j m z hz =>
    (pushA_analytic A hq j (hDO j m hz).1 (hTc _ (hDO j m hz).2)).differentiableAt
  have hintT := fun j => pushA_intOn A P Φ g hg j
  have hintO : ∀ j, IntegrableOn
      (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y)
      (⋃ m, D j m) := fun j => (hintT j).mono_set (by rw [hDU j]; exact Set.inter_subset_left)

  have hpc : ∀ j m, Integrable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} ∩ (A.chart j).symm '' D j m, h j x) ∧
      ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} ∩ (A.chart j).symm '' D j m, h j x =
        ∫ y in D j m, P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y ∧
      ∫ y, ‖∑ᶠ x ∈ q ⁻¹' {y} ∩ (A.chart j).symm '' D j m, h j x‖ =
        ∫ y in D j m, ‖P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y‖ := by
    intro j m
    obtain ⟨hI, hJ⟩ := pushA_piece q (A.chart j).symm (hDm j m) (hdiff j m) (hDi j m) (h j)
    obtain ⟨-, hJ'⟩ := pushA_piece q (A.chart j).symm (hDm j m) (hdiff j m) (hDi j m)
      (fun x => |h j x|)
    refine ⟨hI.2 (((hintT j).mono_set fun z hz => (hDO j m hz).1).congr_fun
      ((hEq j).mono (hDO j m)).symm (hDm j m)), ?_, ?_⟩
    · rw [hJ, setIntegral_congr_fun (hDm j m) ((hEq j).mono (hDO j m))]
    · rw [funext fun y => pushA_piece_norm q (A.chart j).symm (hDi j m) (h j) y, hJ',
        setIntegral_congr_fun (hDm j m) ((hEqN j).mono (hDO j m))]

  have hEd : ∀ j, Pairwise (Function.onFun Disjoint fun m => (A.chart j).symm '' D j m) := by
    intro j m m' hmm'
    refine Set.disjoint_left.2 ?_
    rintro x ⟨z, hz, rfl⟩ ⟨z', hz', hzz⟩
    have : z' = z := by
      rw [← (A.chart j).right_inv (hDO j m' hz').1, hzz, (A.chart j).right_inv (hDO j m hz).1]
    exact Set.disjoint_left.1 (hDd j hmm') hz (this ▸ hz')
  have hEU : ∀ j, ∀ x, x ∉ S → (⋃ m, (A.chart j).symm '' D j m).indicator (h j) x = h j x := by
    intro j x hx
    by_cases hxs : x ∈ (A.chart j).source
    · have hz : A.chart j x ∈ ⋃ m, D j m := by
        rw [hDU j]
        exact ⟨(A.chart j).map_source hxs,
          show (A.chart j).symm (A.chart j x) ∈ Sᶜ by rw [(A.chart j).left_inv hxs]; exact hx⟩
      obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hz
      have hxU : x ∈ ⋃ m, (A.chart j).symm '' D j m :=
        Set.mem_iUnion.2 ⟨m, A.chart j x, hm, (A.chart j).left_inv hxs⟩
      exact Set.indicator_of_mem hxU _
    · have hn : x ∉ ⋃ m, (A.chart j).symm '' D j m := by
        rintro hx'
        obtain ⟨m, z, hz, rfl⟩ := Set.mem_iUnion.1 hx'
        exact hxs ((A.chart j).map_target (hDO j m hz).1)
      rw [Set.indicator_of_notMem hn]
      simp only [hh]
      rw [image_eq_zero_of_notMem_tsupport (fun h' => hxs (P.tsupport_subset j h'))]
      ring

  have hser : ∀ j y, HasSum (fun m => ∑ᶠ x ∈ q ⁻¹' {y} ∩ (A.chart j).symm '' D j m, h j x)
      (∑ᶠ x ∈ q ⁻¹' {y} \ S, h j x) := by
    intro j y
    have hset : ∀ m, q ⁻¹' {y} ∩ (A.chart j).symm '' D j m =
        (q ⁻¹' {y} \ S) ∩ (A.chart j).symm '' D j m := by
      intro m
      ext x
      constructor
      · rintro ⟨hx1, z, hz, rfl⟩
        exact ⟨⟨hx1, (hDO j m hz).2⟩, z, hz, rfl⟩
      · rintro ⟨⟨hx1, -⟩, hx2⟩
        exact ⟨hx1, hx2⟩
    simp only [hset, pushA_finsum_inter, finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
    refine hasSum_sum fun x hx => ?_
    have hxS : x ∉ S := ((hfin y).mem_toFinset.1 hx).2
    rw [← hEU j x hxS]
    exact pushA_hasSum_ind _ (hEd j) (h j) x
  have hnsum : ∀ j, Summable fun m =>
      ∫ y, ‖∑ᶠ x ∈ q ⁻¹' {y} ∩ (A.chart j).symm '' D j m, h j x‖ := by
    intro j
    simp only [fun m => (hpc j m).2.2]
    exact (hasSum_integral_iUnion (hDm j) (hDd j) (hintO j).norm).summable
  have hts : ∀ j, Integrable fun y => ∑' m, ∑ᶠ x ∈ q ⁻¹' {y} ∩ (A.chart j).symm '' D j m, h j x :=
    fun j => pushA_intTsum (fun m => (hpc j m).1) (fun y => (hser j y).summable) (hnsum j)
  have hpt : ∀ y, ∑ j, ∑' m, ∑ᶠ x ∈ q ⁻¹' {y} ∩ (A.chart j).symm '' D j m, h j x =
      ∑ᶠ x ∈ q ⁻¹' {y} \ S, g x * pushDens A Φ q x := by
    intro y
    rw [Finset.sum_congr rfl fun j _ => (hser j y).tsum_eq, pushA_sum_finsum (hfin y)]
    refine finsum_mem_congr rfl fun x _ => ?_
    simp only [hh, ← Finset.sum_mul, P.sum_eq_one, one_mul]
  have hfun : (fun y => ∑ᶠ x ∈ q ⁻¹' {y} \ S, g x * pushDens A Φ q x) =
      fun y => ∑ j, ∑' m, ∑ᶠ x ∈ q ⁻¹' {y} ∩ (A.chart j).symm '' D j m, h j x :=
    funext fun y => (hpt y).symm
  rw [hfun]
  refine ⟨integrable_finsetSum _ fun j _ => hts j, ?_⟩
  rw [integral_finsetSum _ fun j _ => hts j, integralWith]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hnull : ((A.chart j).target : Set (Fin e → ℂ)) =ᵐ[volume]
      (((A.chart j).target ∩ (A.chart j).symm ⁻¹' Sᶜ : Set (Fin e → ℂ))) := by
    refine ae_eq_set.2 ⟨measure_mono_null ?_ (analyticNull A S hS hint j), ?_⟩
    · rintro z ⟨hz, hzO⟩
      have hzS : (A.chart j).symm z ∈ S := by
        by_contra hc
        exact hzO ⟨hz, hc⟩
      exact ⟨(A.chart j).symm z, ⟨hzS, (A.chart j).map_target hz⟩, (A.chart j).right_inv hz⟩
    · rw [Set.sdiff_eq_empty.2 Set.inter_subset_left]
      exact measure_empty
  rw [setIntegral_congr_set hnull, ← hDU j, integral_iUnion (hDm j) (hDd j) (hintO j),
    ← integral_tsum_of_summable_integral_norm (fun m => (hpc j m).1) (hnsum j)]
  exact tsum_congr fun m => ((hpc j m).2.1).symm
end ReciprocityTheory.AnForm.M
