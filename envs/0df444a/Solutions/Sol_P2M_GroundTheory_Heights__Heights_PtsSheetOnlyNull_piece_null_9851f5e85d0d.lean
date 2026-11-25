-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_piece_null_9851f5e85d0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:39:09.488428+00:00
-- url     : https://prove2.me/submissions/79b66463-707f-498e-a9db-e83e47522517

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StCriticalFibreInfinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsSheetOnlyNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_differentiableAt_proj_segre_36c3e8284232
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_differentiableAt_ratio_f91644499ea4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_exists_injective_67792887b40a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_exists_proj_ne_zero_40f19f1ce188
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_isSimpleSheetPt_of_injective_6b1dc600c13c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_analyticOnNhd_det_jacC_ddf5e32b96d3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_injective_iff_det_ne_zero_4dda9d931b27
import Theorems.Thm_ReciprocityTheory_AnForm_A_det_jacC
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood
import Theorems.Thm_ReciprocityTheory_AnForm_volume_eq_zero_of_locally_in_analytic_zero_set
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibreFinite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_osgood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_scaleBlock_mem_zeroLocus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_differentiableAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj IsMultiHomogIdeal mcPts segre fibre IsSheet scaleBlock
  scaleBlock_mem_zeroLocus segre_differentiableAt osgood fibreFinite)
open GroundTheory.Heights₂.Heights.PtsSheetOnlyNull
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
namespace GroundTheory.Heights₂.Heights.PtsSheetOnlyNull
theorem _root_.solution (hC : CriticalFibreInfinite.Statement) {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ' : IsGoodProj P Ψ')
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {O : Set ((Fin e → ℂ) × (((k : K) → ι k) → ℂ))} (hOo : IsOpen O)
    (hO : ∀ q ∈ O, (DifferentiableAt ℂ γ q.1 ∧ γ q.1 ∈ mcPts P ∧ Ψ (segre (γ q.1)) = Fin.cons 1 q.1) ∧
      (q.2 ∈ fibre P Ψ q.1 → q.2 = segre (γ q.1))) :
    volume {y | (y, segre (γ y)) ∈ O ∧
      ¬ IsSimpleSheetPt P Ψ' ((Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y))} = 0 := by
  set τ : (Fin e → ℂ) → Fin e → ℂ := fun y' => ratio (Ψ' (segre (γ y'))) with hτdef
  set B := Prod.fst '' O with hBdef
  have hBo : IsOpen B := isOpenMap_fst O hOo
  have hγB : ∀ y ∈ B, DifferentiableAt ℂ γ y ∧ γ y ∈ mcPts P ∧ Ψ (segre (γ y)) = Fin.cons 1 y := by
    rintro _ ⟨q, hq, rfl⟩
    exact (hO q hq).1
  have hgc : ContinuousOn (fun y => (y, segre (γ y))) B := fun y hy =>
    (continuousAt_id.prodMk (segre_differentiableAt (hγB y hy).1).continuousAt).continuousWithinAt
  set D := B ∩ (fun y => (y, segre (γ y))) ⁻¹' O with hDdef
  have hDo : IsOpen D := hgc.isOpen_inter_preimage hBo hOo
  have hcont0 : ContinuousOn (fun y' => Ψ' (segre (γ y')) 0) B := fun y' hy' =>
    (differentiableAt_pi.1 (differentiableAt_proj_segre Ψ' (hγB y' hy').1) 0).continuousAt.continuousWithinAt
  have hsub : {y | (y, segre (γ y)) ∈ O ∧ ¬ IsSimpleSheetPt P Ψ' ((Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y))} ⊆
      {y | y ∈ D ∧ Ψ' (segre (γ y)) 0 = 0} ∪
        {y | y ∈ D ∧ Ψ' (segre (γ y)) 0 ≠ 0 ∧ ¬ Function.Injective (fderiv ℂ τ y)} := by
    rintro y ⟨hyO, hns⟩
    have hyD : y ∈ D := ⟨⟨_, hyO, rfl⟩, hyO⟩
    by_cases h0 : Ψ' (segre (γ y)) 0 = 0
    · exact Or.inl ⟨hyD, h0⟩
    · refine Or.inr ⟨hyD, h0, fun hinj => hns ?_⟩
      have huniq : ∀ᶠ q in 𝓝 (y, segre (γ y)), q.2 ∈ fibre P Ψ q.1 → q.2 = segre (γ q.1) :=
        Filter.mem_of_superset (hOo.mem_nhds hyO) fun q hq => (hO q hq).2
      exact isSimpleSheetPt_of_injective hP hBo hγB hyD.1 huniq h0 hinj
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
    rintro y ⟨hyD, -⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hDo y hyD
    refine ⟨Metric.ball y r, Metric.isOpen_ball, Metric.mem_ball_self hr, (convex_ball y r).isPreconnected,
      fun y' => Ψ' (segre (γ y')) 0, ?_, ?_, fun y' hy' => hy'.1.2⟩
    · exact (osgood e D _ hDo (fun y' hy' => (differentiableAt_pi.1
        (differentiableAt_proj_segre Ψ' (hγB y' hy'.1).1) 0).differentiableWithinAt)).mono hball
    · exact exists_proj_ne_zero hC hP hΨ' Metric.isOpen_ball (fun y' hy' => hγB y' (hball hy').1)
        (Metric.mem_ball_self hr)
  · apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
    rintro y ⟨hyD, hy0, -⟩
    have hD'o : IsOpen (D ∩ (fun y' => Ψ' (segre (γ y')) 0) ⁻¹' {0}ᶜ) :=
      (hcont0.mono Set.inter_subset_left).isOpen_inter_preimage hDo isOpen_compl_singleton
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hD'o y ⟨hyD, hy0⟩
    have hτd : DifferentiableOn ℂ τ (D ∩ (fun y' => Ψ' (segre (γ y')) 0) ⁻¹' {0}ᶜ) := fun y' hy' =>
      (differentiableAt_ratio Ψ' (hγB y' hy'.1.1).1 hy'.2).differentiableWithinAt
    refine ⟨Metric.ball y r, Metric.isOpen_ball, Metric.mem_ball_self hr, (convex_ball y r).isPreconnected,
      fun y' => (ReciprocityTheory.AnForm.A.jacC τ y').det,
      (SheetOnlyNull.analyticOnNhd_det_jacC hD'o hτd).mono hball, ?_, ?_⟩
    · obtain ⟨y1, hy1, hinj⟩ := exists_injective hC hP hΨ' Metric.isOpen_ball ⟨y, Metric.mem_ball_self hr⟩
        (fun y' hy' => hγB y' (hball hy').1.1) (fun y' hy' => (hball hy').2)
      refine ⟨y1, hy1, ?_⟩
      show (ReciprocityTheory.AnForm.A.jacC τ y1).det ≠ 0
      rw [ReciprocityTheory.AnForm.A.det_jacC]
      exact (SheetOnlyNull.injective_iff_det_ne_zero _).1 hinj
    · rintro y' ⟨⟨-, -, hni⟩, -⟩
      show (ReciprocityTheory.AnForm.A.jacC τ y').det = 0
      rw [ReciprocityTheory.AnForm.A.det_jacC]
      by_contra hne
      exact hni ((SheetOnlyNull.injective_iff_det_ne_zero _).2 hne)
end GroundTheory.Heights₂.Heights.PtsSheetOnlyNull
