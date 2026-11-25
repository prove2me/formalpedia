-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_lintegral_chart_change_e9133996c1cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:35:09.729565+00:00
-- url     : https://prove2.me/submissions/122acfb9-3b61-4db9-a542-3f3cad7936b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ChartMongeAmpereL1Hypotheses
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_AestronglyMeasurableMapSymm
import Theorems.Thm_ReciprocityTheory_AnForm_A_lintegral_image_eq_lintegral_normSq_det_mul
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot maMeasure ChartPartition locDens)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartMongeAmpereL1Measure
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartMongeAmpereL1Measure
theorem _root_.solution {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    (a b : OpenPartialHomeomorph X (Fin D → ℂ))
    (hab : AnalyticOnNhd ℂ (a ∘ b.symm) (b.target ∩ b.symm ⁻¹' a.source))
    {K M : Set X} (hK : IsClosed K) (hKa : K ⊆ a.source) (hM : IsOpen M)
    (hMb : closure M ⊆ b.source) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ F : X → ℝ≥0∞,
      ∫⁻ y in a.target, (K ∩ M).indicator F (a.symm y) ≤
        B * ∫⁻ z in b.target ∩ b.symm ⁻¹' M, F (b.symm z) := by
  set τ : (Fin D → ℂ) → (Fin D → ℂ) := a ∘ b.symm with hτ
  set O := b.target ∩ b.symm ⁻¹' a.source with hO
  have hOo : IsOpen O := b.isOpen_inter_preimage_symm a.open_source
  set J : (Fin D → ℂ) → ℝ := fun z => Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det with hJ
  have hJc : ContinuousOn J O := by
    have hfd : ContinuousOn (fun z => fderiv ℂ τ z) O :=
      (hab.contDiffOn (n := 1) hOo.uniqueDiffOn).continuousOn_fderiv_of_isOpen hOo le_rfl
    have hjac : ContinuousOn (fun z => ReciprocityTheory.AnForm.A.jacC τ z) O := by
      refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun k => ?_
      exact (continuous_apply i).comp_continuousOn (hfd.clm_apply continuousOn_const)
    exact Complex.continuous_normSq.comp_continuousOn
      ((continuous_id.matrix_det).comp_continuousOn hjac)
  set L := b '' (K ∩ closure M) with hL
  have hLc : IsCompact L :=
    (hK.inter isClosed_closure).isCompact.image_of_continuousOn
      (b.continuousOn.mono (inter_subset_right.trans hMb))
  have hLO : L ⊆ O := by
    rintro _ ⟨x, ⟨hxK, hxM⟩, rfl⟩
    refine ⟨b.map_source (hMb hxM), ?_⟩
    simp only [mem_preimage, b.left_inv (hMb hxM)]
    exact hKa hxK
  obtain ⟨C, hC⟩ := hLc.exists_bound_of_continuousOn (hJc.mono hLO)
  set U := b.target ∩ b.symm ⁻¹' (a.source ∩ M) with hU
  have hUo : IsOpen U := b.isOpen_inter_preimage_symm (a.open_source.inter hM)
  have hUO : U ⊆ O := fun z hz => ⟨hz.1, hz.2.1⟩
  have hinj : InjOn τ U := by
    intro z hz z' hz' h
    have h1 : b.symm z = b.symm z' := a.injOn hz.2.1 hz'.2.1 h
    rw [← b.right_inv hz.1, ← b.right_inv hz'.1, h1]
  set V := a.target ∩ a.symm ⁻¹' M with hV
  have hVo : IsOpen V := a.isOpen_inter_preimage_symm hM
  have hτU : τ '' U = V := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨a.map_source hz.2.1, ?_⟩
      simp only [hτ, Function.comp_apply, mem_preimage, a.left_inv hz.2.1]
      exact hz.2.2
    · rintro ⟨hy, hyM⟩
      have hys : a.symm y ∈ b.source := subset_closure.trans hMb hyM
      refine ⟨b (a.symm y), ⟨b.map_source hys, ?_⟩, ?_⟩
      · simp only [mem_preimage, b.left_inv hys]
        exact ⟨a.map_target hy, hyM⟩
      · simp only [hτ, Function.comp_apply, b.left_inv hys, a.right_inv hy]
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun F => ?_⟩
  set f : (Fin D → ℂ) → ℝ≥0∞ := fun y => (K ∩ M).indicator F (a.symm y) with hf
  have h1 : ∫⁻ y in a.target, f y ≤ ∫⁻ y in V, f y := by
    have hc : ∫⁻ y in a.target, f y = ∫⁻ y in a.target, V.indicator f y := by
      refine setLIntegral_congr_fun a.open_target.measurableSet fun y hy => ?_
      by_cases hyM : a.symm y ∈ M
      · rw [indicator_of_mem (show y ∈ V from ⟨hy, hyM⟩)]
      · rw [indicator_of_notMem (fun h : y ∈ V => hyM h.2)]
        simp [hf, indicator_of_notMem (fun h : a.symm y ∈ K ∩ M => hyM h.2)]
    rw [hc, ← lintegral_indicator hVo.measurableSet]
    exact setLIntegral_le_lintegral _ _
  refine h1.trans ?_
  rw [← hτU, ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_normSq_det_mul τ U hUo
    (hab.mono hUO) hinj f]
  calc ∫⁻ z in U, ENNReal.ofReal (Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det) * f (τ z)
      ≤ ∫⁻ z in U, ENNReal.ofReal C * F (b.symm z) := by
        refine setLIntegral_mono' hUo.measurableSet fun z hz => ?_
        have hfz : f (τ z) = (K ∩ M).indicator F (b.symm z) := by
          simp only [hf, hτ, Function.comp_apply, a.left_inv hz.2.1]
        rw [hfz]
        by_cases hzK : b.symm z ∈ K ∩ M
        · rw [indicator_of_mem hzK]
          have hzL : z ∈ L := ⟨b.symm z, ⟨hzK.1, subset_closure hzK.2⟩, b.right_inv hz.1⟩
          have := hC z hzL
          rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)] at this
          gcongr
        · rw [indicator_of_notMem hzK, mul_zero]
          exact zero_le
    _ = ENNReal.ofReal C * ∫⁻ z in U, F (b.symm z) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * ∫⁻ z in b.target ∩ b.symm ⁻¹' M, F (b.symm z) :=
        by gcongr; exact fun z hz => ⟨hz.1, hz.2.2⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartMongeAmpereL1Measure
