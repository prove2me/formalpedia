-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.maMeasure_converse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:14:30.786551+00:00
-- url     : https://prove2.me/submissions/28c554b8-97cf-40c6-b03f-871bfd8912cf

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Theorems.Thm_ReciprocityTheory_AnForm_M_maMeasure_eq_sum
import Theorems.Thm_ReciprocityTheory_AnForm_M_map_withDensity_integrable_integral
import Theorems.Thm_ReciprocityTheory_AnForm_M_chi_comp_continuousOn
import Theorems.Thm_ReciprocityTheory_AnForm_M_existsPartition
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDensChart
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDensCont
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDens_nonneg_of_psh

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Set Filter Topology
open scoped ContDiff ENNReal NNReal
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [T2Space X]
private theorem absDet_clm_fin {e : ℕ} (f : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
    |(f.restrictScalars ℝ).det| = ‖LinearMap.det (f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2 := by
  have h : (f.restrictScalars ℝ).det =
      Algebra.norm ℝ (LinearMap.det (f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) := by
    first
      | exact LinearMap.det_restrictScalars
      | exact LinearMap.det_restrictScalars (f := (f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)))
  rw [h, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  exact abs_of_nonneg (by positivity)
end
end ReciprocityTheory.AnForm.M
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Set Filter Topology
open scoped ContDiff ENNReal NNReal
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [T2Space X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (hPsh : ∀ i, IsPsh A (Φ i)) {g : X → ℝ} (hg : Measurable g)
    (hgi : Integrable g (maMeasure A Φ)) : MIntegrable A Φ g := by
  have hne : Nonempty (ChartPartition A) := existsPartition A
  have hle : ∀ k, chartMeasure A hne.some Φ k ≤ maMeasure A Φ := by
    intro k
    rw [maMeasure_eq_sum A Φ hne, Measure.le_iff']
    intro s
    simp only [Measure.coe_finset_sum, Finset.sum_apply]
    exact Finset.single_le_sum (f := fun i => chartMeasure A hne.some Φ i s)
      (fun _ _ => by simp) (Finset.mem_univ k)
  have hF : ∀ k, IntegrableOn (fun z => g ((A.chart k).symm z) *
      (hne.some.χ k ((A.chart k).symm z) * locDens A Φ k z)) (A.chart k).target := by
    intro k
    have hw0 : ∀ y ∈ (A.chart k).target,
        0 ≤ hne.some.χ k ((A.chart k).symm y) * locDens A Φ k y :=
      fun y hy => mul_nonneg (hne.some.nonneg k _) (locDens_nonneg_of_psh A Φ hΦ hPsh k hy)
    have hw : ContinuousOn (fun y => hne.some.χ k ((A.chart k).symm y) * locDens A Φ k y)
        (A.chart k).target :=
      (chi_comp_continuousOn hne.some k).mul (locDensCont A Φ hΦ k)
    have h1 := (map_withDensity_integrable_integral (A.chart k).open_target
      (A.chart k).continuousOn_symm hw hw0 hg).1
    exact h1.1 (hgi.mono_measure (hle k))
  intro j K hKs hK
  have hKm : MeasurableSet K := hK.measurableSet
  have hterm : ∀ k, IntegrableOn (fun y => hne.some.χ k ((A.chart j).symm y) *
      (g ((A.chart j).symm y) * locDens A Φ j y)) K := by
    intro k
    have hUo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) :=
      (A.chart j).isOpen_inter_preimage_symm (A.chart k).open_source
    have hSm : MeasurableSet (K ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source)) :=
      hKm.inter hUo.measurableSet
    have hder : ∀ y ∈ K ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source),
        HasFDerivWithinAt (A.chart k ∘ (A.chart j).symm)
          ((fderiv ℂ (A.chart k ∘ (A.chart j).symm) y).restrictScalars ℝ)
          (K ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source)) y := by
      intro y hy
      exact (((A.holo j k y hy.2).differentiableAt.hasFDerivAt).restrictScalars ℝ).hasFDerivWithinAt
    have hinj : Set.InjOn (A.chart k ∘ (A.chart j).symm)
        (K ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source)) := by
      intro y hy y' hy' h
      have h1 : (A.chart j).symm y = (A.chart j).symm y' :=
        (A.chart k).injOn hy.2.2 hy'.2.2 h
      exact (A.chart j).symm.injOn hy.2.1 hy'.2.1 h1
    have hcv := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (μ := volume) hSm hder hinj
      (fun z => g ((A.chart k).symm z) *
        (hne.some.χ k ((A.chart k).symm z) * locDens A Φ k z))).1
      ((hF k).mono_set (by
        rintro _ ⟨y, hy, rfl⟩
        exact (A.chart k).map_source hy.2.2))
    have hS' : IntegrableOn (fun y => hne.some.χ k ((A.chart j).symm y) *
        (g ((A.chart j).symm y) * locDens A Φ j y))
        (K ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source)) := by
      refine hcv.congr_fun (fun y hy => ?_) hSm
      have hl : (A.chart k).symm (A.chart k ((A.chart j).symm y)) = (A.chart j).symm y :=
        (A.chart k).left_inv hy.2.2
      simp only [smul_eq_mul, Function.comp_apply]
      rw [hl, locDensChart A Φ hΦ j k y hy.2.1 hy.2.2, absDet_clm_fin]
      ring
    refine hS'.of_forall_diff_eq_zero hKm ?_
    intro y hy
    have hyt : y ∈ (A.chart j).target := hKs hy.1
    have hnot : (A.chart j).symm y ∉ (A.chart k).source := fun h => hy.2 ⟨hy.1, hyt, h⟩
    have h0 : hne.some.χ k ((A.chart j).symm y) = 0 := by
      first
        | exact image_eq_zero_of_notMem_tsupport (fun h => hnot (hne.some.tsupport_subset k h))
        | exact image_eq_zero_of_nmem_tsupport (fun h => hnot (hne.some.tsupport_subset k h))
    rw [h0, zero_mul]
  have hsum : IntegrableOn (fun y => ∑ k, hne.some.χ k ((A.chart j).symm y) *
      (g ((A.chart j).symm y) * locDens A Φ j y)) K :=
    integrable_finset_sum Finset.univ (fun k _ => hterm k)
  refine hsum.congr_fun (fun y _ => ?_) hKm
  simp only
  rw [← Finset.sum_mul, hne.some.sum_eq_one, one_mul]
end ReciprocityTheory.AnForm.M
