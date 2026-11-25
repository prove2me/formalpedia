-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.loc_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:54:50.98829+00:00
-- url     : https://prove2.me/submissions/51f95deb-1f19-4875-a545-7ab6d488212f

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_d_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_db_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_locL2_of_le_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_tsupport_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_continuous_wedge
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
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
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
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
namespace ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
private theorem chart_symm_eventuallyEq_at_chart_point {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (he' : IsChart n z e') (y : M)
    (hy : y ∈ e.source) (hy' : y ∈ e'.source) : e'.symm =ᶠ[𝓝 (z y)] e.symm := by
  have hzy : z y = e y := he hy
  have hzy' : z y = e' y := he' hy'
  have h1 : ∀ᶠ w in 𝓝 (z y), w ∈ e.target := by
    rw [hzy]
    exact e.open_target.mem_nhds (e.map_source hy)
  have h2 : ∀ᶠ w in 𝓝 (z y), w ∈ e'.target := by
    rw [hzy']
    exact e'.open_target.mem_nhds (e'.map_source hy')
  have ht : Tendsto e'.symm (𝓝 (z y)) (𝓝 y) := by
    rw [hzy']
    first
    | exact e'.tendsto_symm hy'
    | (have hc' : Tendsto e'.symm (𝓝 (e' y)) (𝓝 (e'.symm (e' y))) := e'.continuousAt_symm (e'.map_source hy')
       rwa [e'.left_inv hy'] at hc')
  have h3 : ∀ᶠ w in 𝓝 (z y), e'.symm w ∈ e.source := ht.eventually (e.open_source.mem_nhds hy)
  filter_upwards [h1, h2, h3] with w hw hw' hw''
  refine e.injOn hw'' (e.map_target hw) ?_
  rw [e.right_inv hw, ← he hw'', he' (e'.map_target hw'), e'.right_inv hw']
private theorem d_eq_wd_at_chart_image {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : M → ℂ)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (y : M) (hy : y ∈ e.source) (j : Fin n) :
    d n z j g y = wd n j (g ∘ e.symm) (e y) := by
  have hc : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source := ⟨e, he, hy⟩
  simp only [d, dif_pos hc]
  have hs := Classical.choose_spec hc
  have hfg : g ∘ (Classical.choose hc).symm =ᶠ[𝓝 (z y)] g ∘ e.symm :=
    (chart_symm_eventuallyEq_at_chart_point n z e (Classical.choose hc) he hs.1 y hy hs.2).fun_comp g
  rw [← he hy]
  unfold wd
  rw [hfg.fderiv_eq]
private theorem db_eq_wdb_at_chart_image {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : M → ℂ)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (y : M) (hy : y ∈ e.source) (j : Fin n) :
    db n z j g y = wdb n j (g ∘ e.symm) (e y) := by
  have hc : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source := ⟨e, he, hy⟩
  simp only [db, dif_pos hc]
  have hs := Classical.choose_spec hc
  have hfg : g ∘ (Classical.choose hc).symm =ᶠ[𝓝 (z y)] g ∘ e.symm :=
    (chart_symm_eventuallyEq_at_chart_point n z e (Classical.choose hc) he hs.1 y hy hs.2).fun_comp g
  rw [← he hy]
  unfold wdb
  rw [hfg.fderiv_eq]
private theorem continuous_d_of_smooth {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : M → ℂ) (hg : Smooth n z g) (j : Fin n) :
    Continuous (fun x => d n z j g x) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  obtain ⟨e, hx, hze⟩ := hz x
  have he : IsChart n z e := fun y _ => by rw [hze]
  have hF : ContinuousOn (fun w => fderiv ℝ (g ∘ e.symm) w) e.target :=
    (hg e he).continuousOn_fderiv_of_isOpen e.open_target (by first | simp | exact_mod_cast le_top | norm_num)
  have h0 : ContinuousOn (fun w => wd n j (g ∘ e.symm) w) e.target := by
    unfold wd
    exact ((hF.clm_apply continuousOn_const).sub (continuousOn_const.mul
      (hF.clm_apply continuousOn_const))).div_const 2
  have hW : ContinuousOn (fun y => wd n j (g ∘ e.symm) (e y)) e.source :=
    h0.comp e.continuousOn (fun y hy => e.map_source hy)
  have hc := hW.continuousAt (e.open_source.mem_nhds hx)
  have hEv : (fun y => wd n j (g ∘ e.symm) (e y)) =ᶠ[𝓝 x] fun y => d n z j g y := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact (d_eq_wd_at_chart_image n z g e he y hy j).symm
  first
  | exact hc.congr hEv
  | exact hc.congr_of_eventuallyEq hEv.symm
  | exact (continuousAt_congr hEv).mp hc
private theorem continuous_db_apply_of_smooth {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : M → ℂ) (hg : Smooth n z g) (j : Fin n) :
    Continuous (fun x => db n z j g x) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  obtain ⟨e, hx, hze⟩ := hz x
  have he : IsChart n z e := fun y _ => by rw [hze]
  have hF : ContinuousOn (fun w => fderiv ℝ (g ∘ e.symm) w) e.target :=
    (hg e he).continuousOn_fderiv_of_isOpen e.open_target (by first | simp | exact_mod_cast le_top | norm_num)
  have h0 : ContinuousOn (fun w => wdb n j (g ∘ e.symm) w) e.target := by
    unfold wdb
    exact ((hF.clm_apply continuousOn_const).add (continuousOn_const.mul
      (hF.clm_apply continuousOn_const))).div_const 2
  have hW : ContinuousOn (fun y => wdb n j (g ∘ e.symm) (e y)) e.source :=
    h0.comp e.continuousOn (fun y hy => e.map_source hy)
  have hc := hW.continuousAt (e.open_source.mem_nhds hx)
  have hEv : (fun y => wdb n j (g ∘ e.symm) (e y)) =ᶠ[𝓝 x] fun y => db n z j g y := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact (db_eq_wdb_at_chart_image n z g e he y hy j).symm
  first
  | exact hc.congr hEv
  | exact hc.congr_of_eventuallyEq hEv.symm
  | exact (continuousAt_congr hEv).mp hc
private theorem continuous_of_smooth_localization {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : M → ℂ) (hg : Smooth n z g) : Continuous g := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  obtain ⟨e, hx, hze⟩ := hz x
  have he : IsChart n z e := fun y _ => by rw [hze]
  have hW : ContinuousOn (fun y => (g ∘ e.symm) (e y)) e.source :=
    (hg e he).continuousOn.comp e.continuousOn (fun y hy => e.map_source hy)
  have hEv : (fun y => (g ∘ e.symm) (e y)) =ᶠ[𝓝 x] g := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp only [Function.comp_apply, e.left_inv hy]
  have hc := hW.continuousAt (e.open_source.mem_nhds hx)
  first
  | exact hc.congr hEv
  | exact hc.congr_of_eventuallyEq hEv.symm
  | exact (continuousAt_congr hEv).mp hc
end
end ReciprocityTheory.L2DbarEstimates.F
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z)
    (hMD : MultDivStatement n M) (hMS : MultSStatement n M) (η : M → ℝ) (hη : SmoothR n z η)
    (hηc : HasCompactSupport η) (T : Set M) (hT : tsupport η ⊆ T)
    (G : M → V n) (D : M → ℂ) (S : M → Fin n → Fin n → ℂ)
    (hG : LocalL2Isometry (vol n z) G) (hD : LocalL2Isometry (vol n z) D) (hS : LocalL2Isometry (vol n z) S)
    (hGD : IsWeakDiv n z G D) (hGS : IsWeakS n z G S) :
    LocalL2Isometry (vol n z) (locG η G) ∧ LocalL2Isometry (vol n z) (locD n z η G D) ∧
      LocalL2Isometry (vol n z) (locS n z η G S) ∧
      IsWeakDiv n z (locG η G) (locD n z η G D) ∧ IsWeakS n z (locG η G) (locS n z η G S) ∧
      HasCompactSupport (locG η G) ∧ HasCompactSupport (locD n z η G D) ∧
      HasCompactSupport (locS n z η G S) ∧
      tsupport (locG η G) ⊆ T ∧ tsupport (locD n z η G D) ⊆ T ∧
      tsupport (locS n z η G S) ⊆ T := by
  have hsm : Smooth n z (fun y => (η y : ℂ)) := hη
  have hCC : Continuous (fun y => (η y : ℂ)) := continuous_of_smooth_localization n z hz _ hsm
  have hz0 : ∀ x, x ∉ tsupport η → η x = 0 := fun x hx => by
    by_contra hne
    exact hx (subset_tsupport η hne)
  have hev : ∀ x, x ∉ tsupport η → (fun y => (η y : ℂ)) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
    intro x hx
    filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hx] with y hy
    simp [hz0 y hy]
  have hd0 : ∀ j x, x ∉ tsupport η → d n z j (fun y => (η y : ℂ)) x = 0 := by
    intro j x hx
    rw [loc_d_congr n z hz j _ _ x (hev x hx)]
    unfold d wd
    split_ifs <;> simp [Function.comp_def]
  have hdb0 : ∀ j x, x ∉ tsupport η → db n z j (fun y => (η y : ℂ)) x = 0 := by
    intro j x hx
    rw [loc_db_congr n z hz j _ _ x (hev x hx)]
    unfold db wdb
    split_ifs <;> simp [Function.comp_def]
  have hdc : ∀ j, Continuous (fun x => d n z j (fun y => (η y : ℂ)) x) := fun j =>
    continuous_d_of_smooth n z hz _ hsm j
  have hdbc : ∀ j, Continuous (fun x => db n z j (fun y => (η y : ℂ)) x) := fun j =>
    continuous_db_apply_of_smooth n z hz _ hsm j
  have hbound : ∀ φ : M → ℂ, Continuous φ → (∀ x, x ∉ tsupport η → φ x = 0) →
      ∃ C, 0 ≤ C ∧ ∀ x, ‖φ x‖ ≤ C := by
    intro φ hφ h0
    have hsub : tsupport φ ⊆ tsupport η := loc_tsupport_sub φ _ (isClosed_tsupport η) h0
    have hcs : HasCompactSupport φ := IsCompact.of_isClosed_subset hηc (isClosed_tsupport _) hsub
    have hex : ∃ C, ∀ x, ‖φ x‖ ≤ C := by
      first
      | exact hφ.bounded_above_of_compact_support hcs
      | (obtain ⟨C, hC⟩ := (hcs.isCompact_range hφ).isBounded.exists_norm_le
         exact ⟨C, fun x => hC _ ⟨x, rfl⟩⟩)
    obtain ⟨C, hC⟩ := hex
    exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩
  obtain ⟨Cη, hCη0, hCη⟩ := hbound _ hCC (fun x hx => by simp [hz0 x hx])
  obtain ⟨K, hK0, hKd, hKdb⟩ : ∃ K : ℝ, 0 ≤ K ∧ (∀ j x, ‖d n z j (fun y => (η y : ℂ)) x‖ ≤ K) ∧
      (∀ j x, ‖db n z j (fun y => (η y : ℂ)) x‖ ≤ K) := by
    choose C1 hC10 hC1 using fun j => hbound _ (hdc j) (hd0 j)
    choose C2 hC20 hC2 using fun j => hbound _ (hdbc j) (hdb0 j)
    refine ⟨∑ j, (C1 j + C2 j), Finset.sum_nonneg fun j _ => add_nonneg (hC10 j) (hC20 j), ?_, ?_⟩
    · intro j x
      have hs : C1 j + C2 j ≤ ∑ i, (C1 i + C2 i) :=
        Finset.single_le_sum (f := fun i => C1 i + C2 i) (fun i _ => add_nonneg (hC10 i) (hC20 i))
          (Finset.mem_univ j)
      linarith [hC1 j x, hC20 j]
    · intro j x
      have hs : C1 j + C2 j ≤ ∑ i, (C1 i + C2 i) :=
        Finset.single_le_sum (f := fun i => C1 i + C2 i) (fun i _ => add_nonneg (hC10 i) (hC20 i))
          (Finset.mem_univ j)
      linarith [hC2 j x, hC10 j]
  have hcoord : ∀ (v : V n) (j : Fin n), ‖v j‖ ≤ ‖v‖ := by
    intro v j
    first
    | exact PiLp.norm_apply_le v j
    | exact PiLp.norm_apply_le_norm v j
    | (rw [EuclideanSpace.norm_eq]
       exact (le_abs_self _).trans (Real.abs_le_sqrt (Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2)
         (fun i _ => sq_nonneg _) (Finset.mem_univ j))))
  have hcoordc : ∀ j : Fin n, Continuous (fun v : V n => v j) := by
    intro j
    first
    | fun_prop
    | exact (EuclideanSpace.proj (𝕜 := ℂ) j).continuous
    | exact PiLp.continuous_apply 2 _ j
    | continuity
  have hGj : ∀ j : Fin n, AEStronglyMeasurable (fun x => G x j) (vol n z) := fun j =>
    (hcoordc j).comp_aestronglyMeasurable hG.1
  have hGm : LocalL2Isometry (vol n z) (locG η G) := by
    refine locL2_of_le_sum (vol n z) (locG η G) G G Cη hG hG (hCC.aestronglyMeasurable.smul hG.1)
      fun x => ?_
    show ‖(η x : ℂ) • G x‖ ≤ Cη * (‖G x‖ + ‖G x‖)
    rw [norm_smul]
    have := mul_le_mul_of_nonneg_right (hCη x) (norm_nonneg (G x))
    nlinarith [mul_nonneg hCη0 (norm_nonneg (G x))]
  have hDmeas : AEStronglyMeasurable (locD n z η G D) (vol n z) := by
    have h2 : AEStronglyMeasurable (fun x => ∑ j, d n z j (fun y => (η y : ℂ)) x * G x j) (vol n z) := by
      first
      | exact Finset.aestronglyMeasurable_sum _ fun j _ => (hdc j).aestronglyMeasurable.mul (hGj j)
      | exact Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hdc j).aestronglyMeasurable.mul (hGj j)
      | exact Finset.aestronglyMeasurable_sum' _ fun j _ => (hdc j).aestronglyMeasurable.mul (hGj j)
    exact (hCC.aestronglyMeasurable.mul hD.1).add h2
  have hDm : LocalL2Isometry (vol n z) (locD n z η G D) := by
    refine locL2_of_le_sum (vol n z) (locD n z η G D) G D (Cη + (n : ℝ) * K) hG hD hDmeas fun x => ?_
    show ‖(η x : ℂ) * D x + ∑ j, d n z j (fun y => (η y : ℂ)) x * G x j‖ ≤
      (Cη + (n : ℝ) * K) * (‖G x‖ + ‖D x‖)
    have e1 : ‖(η x : ℂ) * D x‖ ≤ Cη * ‖D x‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hCη x) (norm_nonneg _)
    have e2 : ‖∑ j, d n z j (fun y => (η y : ℂ)) x * G x j‖ ≤ (n : ℝ) * K * ‖G x‖ := by
      refine (norm_sum_le _ _).trans ?_
      have hj : ∀ j ∈ Finset.univ, ‖d n z j (fun y => (η y : ℂ)) x * G x j‖ ≤ K * ‖G x‖ := by
        intro j _
        rw [norm_mul]
        exact mul_le_mul (hKd j x) (hcoord (G x) j) (norm_nonneg _) hK0
      refine (Finset.sum_le_sum hj).trans (le_of_eq ?_)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hnK : 0 ≤ (n : ℝ) * K := mul_nonneg (Nat.cast_nonneg n) hK0
    refine (norm_add_le _ _).trans ?_
    nlinarith [norm_nonneg (G x), norm_nonneg (D x), mul_nonneg hCη0 (norm_nonneg (G x)),
      mul_nonneg hnK (norm_nonneg (D x))]
  have hSmeas : AEStronglyMeasurable (locS n z η G S) (vol n z) := by
    have h1 : AEStronglyMeasurable (fun x => fun l => db n z l (fun y => (η y : ℂ)) x) (vol n z) :=
      (continuous_pi fun l => hdbc l).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun x => fun l => G x l) (vol n z) :=
      (continuous_pi fun l => hcoordc l).comp_aestronglyMeasurable hG.1
    have hpair : AEStronglyMeasurable
        (fun x => ((fun l => db n z l (fun y => (η y : ℂ)) x), (fun l => G x l))) (vol n z) := by
      first
      | exact h1.prodMk h2
      | exact h1.prod_mk h2
    have hW := (loc_continuous_wedge n).comp_aestronglyMeasurable hpair
    exact (hCC.aestronglyMeasurable.smul hS.1).add hW
  have hSm : LocalL2Isometry (vol n z) (locS n z η G S) := by
    refine locL2_of_le_sum (vol n z) (locS n z η G S) G S (Cη + 2 * K) hG hS hSmeas fun x => ?_
    have hc0 : 0 ≤ (Cη + 2 * K) * (‖G x‖ + ‖S x‖) :=
      mul_nonneg (by linarith) (add_nonneg (norm_nonneg _) (norm_nonneg _))
    refine (pi_norm_le_iff_of_nonneg hc0).mpr fun j => (pi_norm_le_iff_of_nonneg hc0).mpr fun k => ?_
    show ‖(η x : ℂ) * S x j k + wedge (fun l => db n z l (fun y => (η y : ℂ)) x) (fun l => G x l) j k‖ ≤ _
    have e1 : ‖(η x : ℂ) * S x j k‖ ≤ Cη * ‖S x‖ := by
      rw [norm_mul]
      exact mul_le_mul (hCη x) ((norm_le_pi_norm (S x j) k).trans (norm_le_pi_norm (S x) j))
        (norm_nonneg _) hCη0
    have e2 : ‖wedge (fun l => db n z l (fun y => (η y : ℂ)) x) (fun l => G x l) j k‖ ≤ 2 * K * ‖G x‖ := by
      simp only [wedge]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have a1 := mul_le_mul (hKdb j x) (hcoord (G x) k) (norm_nonneg _) hK0
      have a2 := mul_le_mul (hKdb k x) (hcoord (G x) j) (norm_nonneg _) hK0
      linarith
    refine (norm_add_le _ _).trans ?_
    nlinarith [norm_nonneg (G x), norm_nonneg (S x), mul_nonneg hCη0 (norm_nonneg (G x)),
      mul_nonneg hK0 (norm_nonneg (S x))]
  have hsubG : tsupport (locG η G) ⊆ tsupport η :=
    loc_tsupport_sub _ _ (isClosed_tsupport η) fun x hx => by
      show (η x : ℂ) • G x = 0
      simp [hz0 x hx]
  have hsubD : tsupport (locD n z η G D) ⊆ tsupport η :=
    loc_tsupport_sub _ _ (isClosed_tsupport η) fun x hx => by
      show (η x : ℂ) * D x + ∑ j, d n z j (fun y => (η y : ℂ)) x * G x j = 0
      simp [hz0 x hx, fun j => hd0 j x hx]
  have hsubS : tsupport (locS n z η G S) ⊆ tsupport η :=
    loc_tsupport_sub _ _ (isClosed_tsupport η) fun x hx => by
      funext j k
      show (η x : ℂ) * S x j k + wedge (fun l => db n z l (fun y => (η y : ℂ)) x) (fun l => G x l) j k = 0
      simp [hz0 x hx, fun j => hdb0 j x hx, wedge]
  exact ⟨hGm, hDm, hSm, hMD z hz η G D hη hG hD hGD, hMS z hz η G S hη hG hS hGS,
    IsCompact.of_isClosed_subset hηc (isClosed_tsupport _) hsubG,
    IsCompact.of_isClosed_subset hηc (isClosed_tsupport _) hsubD,
    IsCompact.of_isClosed_subset hηc (isClosed_tsupport _) hsubS,
    hsubG.trans hT, hsubD.trans hT, hsubS.trans hT⟩
end ReciprocityTheory.L2DbarEstimates.F
