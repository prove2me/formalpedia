-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_proof_c8825fc71a8d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:07:50.086744+00:00
-- url     : https://prove2.me/submissions/63c394d1-ebc7-4724-82bc-6abbe23d313c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetImageAreaSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetImageAreaSetFrame
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGraphAreaHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPiece
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGraphJacContinuous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetImageAreaSet
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphBound_proof_3141fa364ca4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPartition_proof_c31322cd93c6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_proof_78929f66b0bb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraph_proof_a2628c3abbdd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_differentiableAt_graphPt_real_10d051ea4057
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_proof_d91937b5f060
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphJacContinuous_proof_b323438eeb5d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_areaJacobian_comp_endo_d99b721ff66c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_areaJacobian_comp_of_norm_5fbe9dbf23fd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_exists_adapted_frame_61c3104c9fe0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Module Matrix
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace SheetImageAreaSet
theorem _root_.solution : SheetImageAreaSet.Statement := by
  classical
  intro n d A U s hU hs hA B hB hBU
  rcases U.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · obtain rfl : B = ∅ := Set.eq_empty_of_forall_notMem fun y hy => hBU y hy
    simp
  let Ue : Set (EuclideanSpace ℂ (Fin d)) := WithLp.ofLp ⁻¹' U
  have hUe : IsOpen Ue := hU.preimage (PiLp.continuous_ofLp 2 _)
  let T : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin n) := fun y => WithLp.toLp 2 (s (WithLp.ofLp y))
  let P : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin d) :=
    (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).symm.toLinearMap ∘ₗ Matrix.mulVecLin A ∘ₗ
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap
  have hPT : ∀ y ∈ Ue, P (T y) = y := fun y hy => by
    simp [P, T, hA _ hy]
  have hPs : Function.Surjective P := by
    have hle : Ue ⊆ (LinearMap.range P : Set _) := fun y hy => ⟨T y, hPT y hy⟩
    refine LinearMap.range_eq_top.1 (Submodule.eq_top_of_nonempty_interior' _
      ⟨WithLp.toLp 2 y₀, interior_mono hle ?_⟩)
    rw [hUe.interior_eq]
    exact hy₀
  obtain ⟨m, e, Q, L, π, hQn, hQ⟩ := SheetImageAreaSet.exists_adapted_frame P hPs
  let F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m) := fun x => π (T (L.symm x))
  let Ω : Set (EuclideanSpace ℂ (Fin d)) := L.symm ⁻¹' Ue
  have hLc : Continuous L.symm := LinearMap.continuous_of_finiteDimensional _
  have hΩ : IsOpen Ω := hUe.preimage hLc
  have hQT : ∀ y ∈ Ue, Q (T y) = graphPt e F (L y) := by
    intro y hy
    rw [hQ, hPT y hy]
    simp [graphPt, F]
  have hsd : ∀ y ∈ Ue, DifferentiableAt ℂ s (WithLp.ofLp y) := fun y hy =>
    hs.differentiableAt (hU.mem_nhds hy)
  have hTd : ∀ y ∈ Ue, DifferentiableAt ℂ T y := fun y hy =>
    (PiLp.hasFDerivAt_toLp (𝕜 := ℂ) 2 _).differentiableAt.comp y
      ((hsd y hy).comp y (PiLp.hasFDerivAt_ofLp (𝕜 := ℂ) 2 y).differentiableAt)
  have hLd : ∀ x, DifferentiableAt ℂ (fun x => L.symm x) x := fun x => by
    simpa using (LinearMap.toContinuousLinearMap L.symm.toLinearMap).differentiableAt (x := x)
  have hπd : ∀ z, DifferentiableAt ℂ (fun z => π z) z := fun z => by
    simpa using (LinearMap.toContinuousLinearMap π).differentiableAt (x := z)
  have hFd : DifferentiableOn ℂ F Ω := fun x hx =>
    ((hπd _).comp x ((hTd _ hx).comp x (hLd x))).differentiableWithinAt
  have hBΩ : L '' B ⊆ Ω := by
    rintro _ ⟨y, hy, rfl⟩
    show L.symm (L y) ∈ Ue
    rw [L.symm_apply_apply]
    exact hBU y hy
  have hLB : MeasurableSet (L '' B) := by
    rw [L.image_eq_preimage_symm]
    exact hLc.measurable hB
  have hQi : Isometry Q := AddMonoidHomClass.isometry_of_norm Q hQn
  have himg : Q '' (T '' B) = graphPt e F '' (L '' B) := by
    rw [Set.image_image, Set.image_image]
    exact Set.image_congr fun y hy => hQT y (hBU y hy)
  have hGA := GraphAreaHolomorphic.proof (AreaGraph.proof
    (AreaGraphBound.proof AreaGraphPiece.proof AreaGraphPartition.proof GraphJacContinuous.proof))
  have hfin : finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2 * d := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have : (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))).IsAddHaarMeasure := by
    have := isAddHaarMeasure_hausdorffMeasure (E := EuclideanSpace ℂ (Fin d))
    rwa [hfin] at this
  let Lr : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin d) :=
    LinearMap.toContinuousLinearMap ((L : _ →ₗ[ℂ] _).restrictScalars ℝ)
  let Qr : EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (Q.restrictScalars ℝ)
  have hCV := lintegral_image_eq_lintegral_abs_det_fderiv_mul (μH[((2 * d : ℕ) : ℝ)]) hB
    (f := fun y => L y) (f' := fun _ => Lr) (fun y _ => Lr.hasFDerivAt.hasFDerivWithinAt) L.injective.injOn
    (fun x => ENNReal.ofReal (areaJacobian (fderiv ℝ (graphPt e F) x :
      EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))))
  rw [← hQi.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg _)), himg,
    hGA d m n e Ω F hΩ hFd (L '' B) hBΩ hLB, hCV]
  refine setLIntegral_congr_fun hB fun y hy => ?_
  have hy' : y ∈ Ue := hBU y hy
  let Mt : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap.comp
      ((fderiv ℝ s (WithLp.ofLp y)).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℂ)).toContinuousLinearMap)
  have hT : HasFDerivAt T Mt y :=
    (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp y
      (((hsd y hy').restrictScalars ℝ).hasFDerivAt.comp y (PiLp.hasFDerivAt_ofLp (𝕜 := ℝ) 2 y))
  have hx : L y ∈ Ω := hBΩ ⟨y, hy, rfl⟩
  have hFR : DifferentiableAt ℝ F (L y) := ((hFd.differentiableAt (hΩ.mem_nhds hx)).restrictScalars ℝ)
  have hG : HasFDerivAt (graphPt e F) (fderiv ℝ (graphPt e F) (L y)) (L y) :=
    (GraphAreaHolomorphic.differentiableAt_graphPt_real e hFR).hasFDerivAt
  have h1 : HasFDerivAt (fun z => Q (T z)) (Qr.comp Mt) y := Qr.hasFDerivAt.comp y hT
  have h2 : HasFDerivAt (fun z => graphPt e F (L z)) ((fderiv ℝ (graphPt e F) (L y)).comp Lr) y :=
    hG.comp y Lr.hasFDerivAt
  have hM : Qr.comp Mt = (fderiv ℝ (graphPt e F) (L y)).comp Lr :=
    h1.unique (h2.congr_of_eventuallyEq (Filter.eventually_of_mem (hUe.mem_nhds hy') fun z hz => hQT z hz))
  have hJ : sheetJac s (WithLp.ofLp y) =
      areaJacobian (Mt : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) :=
    congrArg areaJacobian (LinearMap.ext fun v => rfl)
  have hJ2 : areaJacobian (Mt : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) =
      areaJacobian (fderiv ℝ (graphPt e F) (L y) : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) *
        |LinearMap.det (Lr : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin d))| := by
    have hQr : ∀ v, ‖(Qr : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) v‖ = ‖v‖ := fun v => by
      simp only [Qr, ContinuousLinearMap.coe_coe, LinearMap.coe_toContinuousLinearMap',
        LinearMap.coe_restrictScalars]
      exact hQn v
    rw [← SheetImageAreaSet.areaJacobian_comp_of_norm _ hQr,
      ← SheetImageAreaSet.areaJacobian_comp_endo]
    rw [← ContinuousLinearMap.toLinearMap_comp, ← ContinuousLinearMap.toLinearMap_comp, hM]
  rw [hJ, hJ2, mul_comm (areaJacobian _), ENNReal.ofReal_mul (abs_nonneg _)]
end SheetImageAreaSet
end GroundTheory.Heights₂.Heights
