-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.degreeFormulaInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:42:59.876122+00:00
-- url     : https://prove2.me/submissions/3999f518-616b-49ab-bb6e-af73b8518271

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeInt
import Theorems.Thm_ReciprocityTheory_AnForm_M_exists_sheet_partition
import Theorems.Thm_ReciprocityTheory_AnForm_M_degree_piece
import Theorems.Thm_ReciprocityTheory_AnForm_M_analyticNull
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_chartDens_abs
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_chartDens_locDens
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_chi_le_one
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_hasSum
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_indicator
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_localize
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_mset
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_sum_ind_le
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_target_of_mIntegrable
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_target_of_weights
import Theorems.Thm_ReciprocityTheory_AnForm_M_existsPartition
import Theorems.Thm_ReciprocityTheory_AnForm_M_integrableOn_weight
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotentialPullback
import Theorems.Thm_ReciprocityTheory_AnForm_M_mIntEq
import Theorems.Thm_ReciprocityTheory_AnForm_M_sheet_lintegral


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
variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : DegreeFormulaIntStatement := by
  intro e X Y _ _ _ _ _ _ A B h hh d S hd Φ hΦ g hg
  rcases isEmpty_or_nonempty X with hX | hX
  · have hY : IsEmpty Y := ⟨fun y => hX.false (h y)⟩
    have hA : ∀ k, (A.chart k).target = ∅ := fun k => by
      rw [← (A.chart k).image_source_eq_target, Set.eq_empty_of_isEmpty (A.chart k).source,
        Set.image_empty]
    have hB : ∀ k, (B.chart k).target = ∅ := fun k => by
      rw [← (B.chart k).image_source_eq_target, Set.eq_empty_of_isEmpty (B.chart k).source,
        Set.image_empty]
    refine ⟨fun j K hK _ => ?_, ?_⟩
    · rw [hB j, Set.subset_empty_iff] at hK
      rw [hK]
      exact integrableOn_empty
    · simp [mInt, integralWith, hA, hB]
  letI : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  letI : MeasurableSpace Y := borel Y
  have : BorelSpace Y := ⟨rfl⟩
  have hΨ : ∀ i, IsPotential B ((Φ i).pullback h hh.1) :=
    fun i => isPotentialPullback A B h hh (Φ i) (hΦ i)
  obtain ⟨P⟩ := existsPartition A
  obtain ⟨Q⟩ := existsPartition B
  obtain ⟨E, V, k, W, j, hEm, hEd, hEU, hEV, hsh⟩ := exists_sheet_partition hh hd
  have hmh : Measurable h := hh.1.measurable
  have hpiece := fun m => degree_piece hh Φ hΦ P Q (hEm m) (hEV m) (hsh m).1 (hsh m).2.1
    (hsh m).2.2.1 (hsh m).2.2.2.1 (hsh m).2.2.2.2.1 (hsh m).2.2.2.2.2 g hg
  have hvX : ∀ m, IntegrableOn (fun z => (E m).indicator g ((A.chart (k m)).symm z) *
      locDens A Φ (k m) z) (A.chart (k m)).target :=
    fun m => dI_indicator (A.chart (k m)) (hEm m) g _ (dI_target_of_mIntegrable A Φ hΦ g hg (k m))
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, ∀ m, a m = ∫ z in (A.chart (k m)).target,
      |(E m).indicator g ((A.chart (k m)).symm z)| * |locDens A Φ (k m) z| := ⟨_, fun m => rfl⟩
  have ha0 : ∀ m, 0 ≤ a m := fun m => by
    rw [ha]
    exact setIntegral_nonneg (A.chart (k m)).open_target.measurableSet
      (fun z _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have haloc : ∀ m, (∀ jj, IntegrableOn (fun z => P.χ jj ((A.chart jj).symm z) *
        |(E m).indicator g ((A.chart jj).symm z)| * |locDens A Φ jj z|) (A.chart jj).target) ∧
      ∑ jj, ∫ z in (A.chart jj).target, P.χ jj ((A.chart jj).symm z) *
        |(E m).indicator g ((A.chart jj).symm z)| * |locDens A Φ jj z| = a m := by
    intro m
    rw [ha]
    refine dI_localize A P (dI_chartDens_abs A (dI_chartDens_locDens A Φ hΦ)) (k m)
      (fun x => |(E m).indicator g x|) (fun x hx => ?_) ?_
    · rw [Set.indicator_of_notMem (fun h' => hx ((hsh m).2.1 (hEV m h'))), abs_zero]
    · refine IntegrableOn.congr_fun (hvX m).norm (fun z _ => ?_) (A.chart (k m)).open_target.measurableSet
      simp only [Real.norm_eq_abs, abs_mul]
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∑ jj, ∫ z in (A.chart jj).target,
      ‖P.χ jj ((A.chart jj).symm z) * g ((A.chart jj).symm z) * locDens A Φ jj z‖ :=
    ⟨_, rfl⟩
  have hsumN : ∀ N, ∑ m ∈ Finset.range N, a m ≤ C := by
    intro N
    rw [hC]
    calc ∑ m ∈ Finset.range N, a m = ∑ jj, ∫ z in (A.chart jj).target, ∑ m ∈ Finset.range N,
          P.χ jj ((A.chart jj).symm z) * |(E m).indicator g ((A.chart jj).symm z)| *
            |locDens A Φ jj z| := by
          rw [Finset.sum_congr rfl (fun m _ => ((haloc m).2).symm), Finset.sum_comm]
          refine Finset.sum_congr rfl (fun jj _ => ?_)
          rw [integral_finsetSum _ (fun m _ => (haloc m).1 jj)]
      _ ≤ _ := by
          refine Finset.sum_le_sum (fun jj _ => ?_)
          refine integral_mono_of_nonneg (Eventually.of_forall fun z => ?_)
            (integrableOn_weight A P Φ g hg jj).norm (Eventually.of_forall fun z => ?_)
          · exact Finset.sum_nonneg (fun m _ =>
              mul_nonneg (mul_nonneg (P.nonneg jj _) (abs_nonneg _)) (abs_nonneg _))
          · simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (P.nonneg jj _)]
            rw [← Finset.sum_mul, ← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              (dI_sum_ind_le E hEd g _ N) (P.nonneg jj _)) (abs_nonneg _)
  have hfin : ∑' m, (d : ENNReal) * ENNReal.ofReal (a m) < ⊤ := by
    rw [ENNReal.tsum_mul_left]
    refine ENNReal.mul_lt_top (ENNReal.natCast_lt_top d) (lt_of_le_of_lt
      (ENNReal.tsum_le_of_sum_range_le (c := ENNReal.ofReal C) fun N => ?_) ENNReal.ofReal_lt_top)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => ha0 m)]
    exact ENNReal.ofReal_le_ofReal (hsumN N)
  have hY : ∀ j', IntegrableOn (fun y => Q.χ j' ((B.chart j').symm y) * (g ∘ h) ((B.chart j').symm y) *
      locDens B (fun i => (Φ i).pullback h hh.1) j' y) (B.chart j').target := by
    intro j'
    have hRm : ∀ m, MeasurableSet ((B.chart j').target ∩ (B.chart j').symm ⁻¹' (h ⁻¹' E m)) :=
      fun m => dI_mset (B.chart j') (hmh (hEm m))
    have hRint : ∀ m, IntegrableOn (fun y => Q.χ j' ((B.chart j').symm y) *
        (g ∘ h) ((B.chart j').symm y) * locDens B (fun i => (Φ i).pullback h hh.1) j' y)
        ((B.chart j').target ∩ (B.chart j').symm ⁻¹' (h ⁻¹' E m)) := by
      intro m
      refine (((hpiece m).1 j').mono_set Set.inter_subset_left).congr_fun (fun y hy => ?_) (hRm m)
      simp only [Function.comp_apply]
      rw [Set.indicator_of_mem (show h ((B.chart j').symm y) ∈ E m from hy.2)]
    have hbound : ∀ m, ∫⁻ y in (B.chart j').target ∩ (B.chart j').symm ⁻¹' (h ⁻¹' E m),
        ‖Q.χ j' ((B.chart j').symm y) * (g ∘ h) ((B.chart j').symm y) *
          locDens B (fun i => (Φ i).pullback h hh.1) j' y‖ₑ ≤ d * ENNReal.ofReal (a m) := by
      intro m
      obtain ⟨hVo, hVk, hWo, hWd, hpre, hsh'⟩ := hsh m
      have s1 : ∫⁻ y in (B.chart j').target ∩ (B.chart j').symm ⁻¹' (h ⁻¹' E m),
          ‖Q.χ j' ((B.chart j').symm y) * (g ∘ h) ((B.chart j').symm y) *
            locDens B (fun i => (Φ i).pullback h hh.1) j' y‖ₑ ≤
          ∫⁻ y in (B.chart j').target ∩ (B.chart j').symm ⁻¹' (h ⁻¹' E m),
            ENNReal.ofReal |(E m).indicator g (h ((B.chart j').symm y))| *
              ENNReal.ofReal |locDens B (fun i => (Φ i).pullback h hh.1) j' y| := by
        refine setLIntegral_mono' (hRm m) (fun y hy => ?_)
        have hyE : h ((B.chart j').symm y) ∈ E m := hy.2
        simp only [Function.comp_apply, Set.indicator_of_mem hyE, enorm_mul,
          Real.enorm_eq_ofReal_abs]
        rw [mul_assoc]
        refine mul_le_of_le_one_left zero_le ?_
        exact ENNReal.ofReal_le_one.2 (by
          rw [abs_of_nonneg (Q.nonneg _ _)]; exact dI_chi_le_one B Q j' _)
      have s2 : (B.chart j').target ∩ (B.chart j').symm ⁻¹' (h ⁻¹' E m) ⊆
          ⋃ i, (B.chart j') '' (W m i ∩ (B.chart j').source) := by
        rintro y ⟨hyt, hyE⟩
        have hyV : (B.chart j').symm y ∈ h ⁻¹' V m := hEV m hyE
        rw [hpre] at hyV
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hyV
        exact Set.mem_iUnion.2 ⟨i, _, ⟨hi, (B.chart j').map_target hyt⟩,
          (B.chart j').right_inv hyt⟩
      have s3 : ∀ i, ∫⁻ y in (B.chart j') '' (W m i ∩ (B.chart j').source),
          ENNReal.ofReal |(E m).indicator g (h ((B.chart j').symm y))| *
            ENNReal.ofReal |locDens B (fun i => (Φ i).pullback h hh.1) j' y| ≤
          ENNReal.ofReal (a m) := by
        intro i
        have hW' : IsOpen (W m i ∩ (B.chart j').source) := (hWo i).inter (B.chart j').open_source
        have hbij : Set.BijOn h (W m i ∩ (B.chart j').source)
            (h '' (W m i ∩ (B.chart j').source)) :=
          ((hsh' i).1.injOn.mono Set.inter_subset_left).bijOn_image
        have hV' : h '' (W m i ∩ (B.chart j').source) ⊆ (A.chart (k m)).source := by
          rintro _ ⟨w, hw, rfl⟩; exact hVk ((hsh' i).1.mapsTo hw.1)
        have hSL := sheet_lintegral hh Φ hΦ j' (k m) hW' Set.inter_subset_right hV' hbij
          (fun x => ENNReal.ofReal |(E m).indicator g x|)
        have hn := ofReal_integral_norm_eq_lintegral_enorm (hvX m)
        have h2 : ∫ z in (A.chart (k m)).target,
            ‖(E m).indicator g ((A.chart (k m)).symm z) * locDens A Φ (k m) z‖ = a m := by
          rw [ha]
          refine setIntegral_congr_fun (A.chart (k m)).open_target.measurableSet (fun z _ => ?_)
          simp only [Real.norm_eq_abs, abs_mul]
        rw [h2] at hn
        calc ∫⁻ y in (B.chart j') '' (W m i ∩ (B.chart j').source),
              ENNReal.ofReal |(E m).indicator g (h ((B.chart j').symm y))| *
                ENNReal.ofReal |locDens B (fun i => (Φ i).pullback h hh.1) j' y|
            = ∫⁻ z in (A.chart (k m)) '' (h '' (W m i ∩ (B.chart j').source)),
              ENNReal.ofReal |(E m).indicator g ((A.chart (k m)).symm z)| *
                ENNReal.ofReal |locDens A Φ (k m) z| := hSL
          _ ≤ ∫⁻ z in (A.chart (k m)).target,
              ENNReal.ofReal |(E m).indicator g ((A.chart (k m)).symm z)| *
                ENNReal.ofReal |locDens A Φ (k m) z| :=
            lintegral_mono_set (by
              rintro _ ⟨x, hx, rfl⟩; exact (A.chart (k m)).map_source (hV' hx))
          _ = ENNReal.ofReal (a m) := by
            rw [hn]
            refine lintegral_congr (fun z => ?_)
            simp only [enorm_mul, Real.enorm_eq_ofReal_abs]
      calc _ ≤ _ := s1
        _ ≤ ∫⁻ y in ⋃ i, (B.chart j') '' (W m i ∩ (B.chart j').source),
              ENNReal.ofReal |(E m).indicator g (h ((B.chart j').symm y))| *
                ENNReal.ofReal |locDens B (fun i => (Φ i).pullback h hh.1) j' y| :=
            lintegral_mono_set s2
        _ ≤ ∑' i, ∫⁻ y in (B.chart j') '' (W m i ∩ (B.chart j').source),
              ENNReal.ofReal |(E m).indicator g (h ((B.chart j').symm y))| *
                ENNReal.ofReal |locDens B (fun i => (Φ i).pullback h hh.1) j' y| :=
            lintegral_iUnion_le _ _
        _ ≤ ∑' i : Fin d, ENNReal.ofReal (a m) := ENNReal.tsum_le_tsum s3
        _ = d * ENNReal.ofReal (a m) := by
            rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hU : IntegrableOn (fun y => Q.χ j' ((B.chart j').symm y) *
        (g ∘ h) ((B.chart j').symm y) * locDens B (fun i => (Φ i).pullback h hh.1) j' y)
        (⋃ m, (B.chart j').target ∩ (B.chart j').symm ⁻¹' (h ⁻¹' E m)) :=
      ⟨AEStronglyMeasurable.iUnion fun m => (hRint m).1,
        (lintegral_iUnion_le _ _).trans_lt ((ENNReal.tsum_le_tsum hbound).trans_lt hfin)⟩
    have hZ := analyticNull B (h ⁻¹' S) hd.2.2.1 hd.2.2.2.1 j'
    have hZint : IntegrableOn (fun y => Q.χ j' ((B.chart j').symm y) *
        (g ∘ h) ((B.chart j').symm y) * locDens B (fun i => (Φ i).pullback h hh.1) j' y)
        ((B.chart j') '' (h ⁻¹' S ∩ (B.chart j').source)) := by
      rw [IntegrableOn, Measure.restrict_eq_zero.2 hZ]
      exact integrable_zero_measure
    refine (hU.union hZint).mono_set (fun y hy => ?_)
    by_cases hyS : (B.chart j').symm y ∈ h ⁻¹' S
    · exact Or.inr ⟨_, ⟨hyS, (B.chart j').map_target hy⟩, (B.chart j').right_inv hy⟩
    · have hyU : h ((B.chart j').symm y) ∈ ⋃ m, E m := by rw [hEU]; exact hyS
      obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hyU
      exact Or.inl (Set.mem_iUnion.2 ⟨m, hy, hm⟩)
  have hXsum : HasSum (fun m => integralWith A P Φ ((E m).indicator g)) (integralWith A P Φ g) :=
    dI_hasSum A P Φ g (fun jj => integrableOn_weight A P Φ g hg jj) E hEm hEd S
      (analyticNull A S hd.1 hd.2.1) hEU
  have hYsum := dI_hasSum B Q (fun i => (Φ i).pullback h hh.1) (g ∘ h) hY (fun m => h ⁻¹' E m)
    (fun m => hmh (hEm m)) (fun m m' hmm' => (hEd hmm').preimage h) (h ⁻¹' S)
    (analyticNull B (h ⁻¹' S) hd.2.2.1 hd.2.2.2.1)
    (by rw [← Set.preimage_iUnion, hEU, Set.preimage_compl])
  have key : ∀ m, integralWith B Q (fun i => (Φ i).pullback h hh.1)
      ((h ⁻¹' E m).indicator (g ∘ h)) = d * integralWith A P Φ ((E m).indicator g) := by
    intro m
    rw [show (h ⁻¹' E m).indicator (g ∘ h) = fun y => (E m).indicator g (h y) from
      funext fun y => Set.indicator_comp_right h]
    exact (hpiece m).2
  simp only [key] at hYsum
  have hMY : MIntegrable B (fun i => (Φ i).pullback h hh.1) (g ∘ h) := fun j' K hK _ =>
    (dI_target_of_weights B Q (dI_chartDens_locDens B _ hΨ) (g ∘ h) hY j').mono_set hK
  refine ⟨hMY, ?_⟩
  rw [mIntEq B Q _ hΨ (g ∘ h) hMY, mIntEq A P Φ hΦ g hg]
  exact HasSum.unique hYsum (hXsum.mul_left _)
end ReciprocityTheory.AnForm.M
