-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fc_mu_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:06:42.592464+00:00
-- url     : https://prove2.me/submissions/e3309095-e3f3-488a-93ef-debff0793a05

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcC
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_det_real
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_rho_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_rho_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_isOpen_O
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_jz_det_ne
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_mem_O
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_zLoc_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_zLoc_contDiffOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_isOpen_Mset
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_lintegral_vol_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_measurableSet_image_of_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s)
    (hF : A.Flat w0 s De) (e : OpenPartialHomeomorph (A.Mset w0 s De) (V n))
    (he : IsChart n (flatStein A hD hF).z e) (i : ι) (B : Set (A.Mset w0 s De))
    (hB : MeasurableSet B) (hBs : B ⊆ e.source) (hBi : ∀ m ∈ B, (m : Y) ∈ (A.chart i).source) :
    A.mu.comap Subtype.val B =
      ∫⁻ m in B, ENNReal.ofReal ((fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) / ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) m) ∂vol n (flatStein A hD hF).z := by
  have hMm : MeasurableSet (A.Mset w0 s De) := (isOpen_Mset A hD).measurableSet
  have hemb := MeasurableEmbedding.subtype_coe hMm
  have hz := (flatStein A hD hF).isLocalHomeomorph
  have hρ : Measurable fun m => ENNReal.ofReal ((fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) / ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) m) :=
    ENNReal.measurable_ofReal.comp (fc_rho_continuous A hD hF).measurable
  rw [hemb.comap_apply]
  have hBY : MeasurableSet (Subtype.val '' B : Set Y) := hemb.measurableSet_image.2 hB
  rw [A.mu_chart i _ hBY (by rintro _ ⟨m, hm, rfl⟩; exact hBi m hm)]
  have hBimg : MeasurableSet (e '' B) := by
    have := measurableSet_image_of_chart n (flatStein A hD hF).z e he B hB hBs
    rwa [Set.image_congr fun m hm => he (hBs hm)] at this
  have hR : ∫⁻ m in B, ENNReal.ofReal ((fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) / ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) m) ∂vol n (flatStein A hD hF).z =
      ∫⁻ w in e '' B, ENNReal.ofReal ((fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) / ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) (e.symm w)) := by
    rw [← lintegral_indicator hB, lintegral_vol_chart n _ hz e he _ (hρ.indicator hB)
      (fun m hm => Set.indicator_of_notMem (fun h => hm (hBs h)) _)]
    have hsub : e '' B ⊆ e.target := fun _ ⟨m, hm, hmw⟩ => hmw ▸ e.map_source (hBs hm)
    rw [← Set.inter_eq_left.2 hsub, ← Measure.restrict_restrict hBimg, ← lintegral_indicator hBimg]
    refine setLIntegral_congr_fun e.open_target.measurableSet fun w hw => ?_
    by_cases h : e.symm w ∈ B
    · have hw' : w ∈ e '' B := ⟨e.symm w, h, e.right_inv hw⟩
      simp only [Set.indicator_of_mem h, Set.indicator_of_mem hw']
    · have hw' : w ∉ e '' B := by
        rintro ⟨m, hm, rfl⟩
        exact h (by rw [e.left_inv (hBs hm)]; exact hm)
      simp only [Set.indicator_of_notMem h, Set.indicator_of_notMem hw']
  set S := A.chart i '' (Subtype.val '' B)
  have hS : MeasurableSet S :=
    measurableSet_image_of_chart n (A.chart i) (A.chart i) (fun _ _ => rfl) _ hBY
      (by rintro _ ⟨m, hm, rfl⟩; exact hBi m hm)
  have hSO : S ⊆ (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De := by
    rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact fc_mem_O A m i (hBi m hm)
  have hFm : ∀ m ∈ B, A.zLoc w0 s i (A.chart i m) = e m := fun m hm =>
    fc_zLoc_chart A hD e he m (hBs hm) i (hBi m hm)
  have himg : e '' B = A.zLoc w0 s i '' S := by
    rw [Set.image_image, Set.image_image]
    exact (Set.image_congr fun m hm => hFm m hm).symm
  have hinj : Set.InjOn (A.zLoc w0 s i) S := by
    rintro _ ⟨_, ⟨m1, hm1, rfl⟩, rfl⟩ _ ⟨_, ⟨m2, hm2, rfl⟩, rfl⟩ h
    rw [hFm m1 hm1, hFm m2 hm2] at h
    rw [e.injOn (hBs hm1) (hBs hm2) h]
  have hder : ∀ v ∈ S, HasFDerivWithinAt (A.zLoc w0 s i)
      ((fderiv ℂ (A.zLoc w0 s i) v).restrictScalars ℝ) S v := fun v hv =>
    ((((fc_zLoc_contDiffOn A hD i).differentiableOn (by simp)).differentiableAt
      ((fc_isOpen_O A hD i).mem_nhds (hSO hv))).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  rw [hR, himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hder hinj]
  refine setLIntegral_congr_fun hS ?_
  rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
  have hne := fc_jz_det_ne A hD hF m.2 i (hBi m hm)
  simp only
  rw [hFm m hm, e.left_inv (hBs hm), (A.chart i).left_inv (hBi m hm),
    fc_rho_eq A hD m.2 i (hBi m hm), ← ENNReal.ofReal_mul (abs_nonneg _), fc_det_real]
  congr 1
  field_simp
end ReciprocityTheory.L2DbarEstimates.Y
