-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AreaFormulaLocal_proof_f6a9378629ed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:54:08.92131+00:00
-- url     : https://prove2.me/submissions/ad7e4ce2-8de3-4d31-808e-ad588f946d1f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPiece
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGraphJacContinuous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetImageAreaSetFrame
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaFormulaLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaFormulaLocal_normDet_comp_of_norm_ca1a2bf1be84
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaFormulaLocal_exists_frame_66efb179ad63
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaFormulaLocal_setLIntegral_image_881958a63272
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphBound_proof_3141fa364ca4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPartition_proof_c31322cd93c6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_normDet_graphLin_eb5fb2a3868a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_proof_78929f66b0bb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraph_proof_a2628c3abbdd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_proof_d91937b5f060
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphJacContinuous_proof_b323438eeb5d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_areaJacobian_eq_normDet_42419aa0db84


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
open MeasureTheory Module Set
open scoped ENNReal
noncomputable section
open AreaFormulaLocal AreaGraphPiece
namespace GroundTheory.Heights₂.Heights
namespace AreaFormulaLocal
theorem _root_.solution : AreaFormulaLocal.Statement := by
  intro E F _ _ _ _ _ _ _ _ _ _ k hk U f x₀ hU hf hx₀ hinj
  classical
  have hAG : AreaGraph.Statement := AreaGraph.proof
    (AreaGraphBound.proof AreaGraphPiece.proof AreaGraphPartition.proof GraphJacContinuous.proof)
  have hfc : ∀ x ∈ U, ContDiffAt ℝ 1 f x := fun x hx => hf.contDiffAt (hU.mem_nhds hx)
  have hfd : ∀ x ∈ U, HasFDerivAt f (fderiv ℝ f x) x := fun x hx =>
    ((hfc x hx).differentiableAt one_ne_zero).hasFDerivAt

  set D := fderiv ℝ f x₀ with hD
  have hWk : finrank ℝ (LinearMap.range (D : E →ₗ[ℝ] F)) = k := by
    rw [LinearMap.finrank_range_of_inj hinj, hk]
  obtain ⟨m, c, c', hcc, hc'⟩ := exists_frame (LinearMap.range (D : E →ₗ[ℝ] F)) hWk
  let Q : F →ₗ[ℝ] EuclideanSpace ℝ (Fin k ⊕ Fin m) :=
    { toFun := fun z => pairPt (c z) (c' z)
      map_add' := fun z w => by rw [map_add, map_add, pairPt_add]
      map_smul' := fun r z => by rw [map_smul, map_smul, pairPt_smul]; rfl }
  have hQ : ∀ z, ‖Q z‖ = ‖z‖ := hcc

  let a : E → EuclideanSpace ℝ (Fin k) := fun x => c (f x)
  have had : ∀ x ∈ U, HasFDerivAt a (c.comp (fderiv ℝ f x)) x := fun x hx =>
    c.hasFDerivAt.comp x (hfd x hx)
  have hinj0 : Function.Injective ((c.comp D : E →L[ℝ] EuclideanSpace ℝ (Fin k)) :
      E →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) := by
    intro v w hvw
    apply hinj
    have hv : D (v - w) ∈ LinearMap.range (D : E →ₗ[ℝ] F) := ⟨v - w, rfl⟩
    have h0 : c (D (v - w)) = 0 := by
      rw [map_sub, map_sub]
      exact sub_eq_zero.2 hvw
    have hz : D (v - w) = 0 := by
      rw [← norm_eq_zero, ← hcc (D (v - w)), h0, hc' _ hv]
      have hp : pairPt (0 : EuclideanSpace ℝ (Fin k)) (0 : EuclideanSpace ℝ (Fin m)) = 0 := by
        ext i
        rcases i with i | i <;> simp [pairPt]
      rw [hp, norm_zero]
    rwa [map_sub, sub_eq_zero] at hz
  have hdim : finrank ℝ E = finrank ℝ (EuclideanSpace ℝ (Fin k)) := by simp [hk]
  let e0 : E ≃L[ℝ] EuclideanSpace ℝ (Fin k) :=
    (LinearMap.linearEquivOfInjective _ hinj0 hdim).toContinuousLinearEquiv
  have he0 : HasFDerivAt a (e0 : E →L[ℝ] EuclideanSpace ℝ (Fin k)) x₀ := by
    convert had x₀ hx₀ using 1
    exact ContinuousLinearMap.ext fun v => rfl
  have hac : ContDiffAt ℝ 1 a x₀ := c.contDiff.contDiffAt.comp x₀ (hfc x₀ hx₀)

  let φ := hac.toOpenPartialHomeomorph a he0 one_ne_zero
  have hφa : (φ : E → EuclideanSpace ℝ (Fin k)) = a := rfl
  have hx₀φ : x₀ ∈ φ.source := hac.mem_toOpenPartialHomeomorph_source he0 one_ne_zero

  let O : Set (E →L[ℝ] EuclideanSpace ℝ (Fin k)) :=
    range ((↑) : (E ≃L[ℝ] EuclideanSpace ℝ (Fin k)) → E →L[ℝ] EuclideanSpace ℝ (Fin k))
  have hcont : ContinuousOn (fun x => c.comp (fderiv ℝ f x)) U :=
    ((ContinuousLinearMap.compL ℝ E F (EuclideanSpace ℝ (Fin k))) c).continuous.comp_continuousOn
      (hf.continuousOn_fderiv_of_isOpen hU le_rfl)
  have hS : IsOpen (U ∩ (fun x => c.comp (fderiv ℝ f x)) ⁻¹' O) :=
    hcont.isOpen_inter_preimage hU ContinuousLinearEquiv.isOpen
  let V : Set E := φ.source ∩ (U ∩ (fun x => c.comp (fderiv ℝ f x)) ⁻¹' O)
  have hVo : IsOpen V := φ.open_source.inter hS
  have hVU : V ⊆ U := fun x hx => hx.2.1
  have hx₀V : x₀ ∈ V := ⟨hx₀φ, hx₀, e0, rfl⟩
  refine ⟨V, hVo, hx₀V, hVU, fun B hBV hB => ?_⟩

  let T : Set (EuclideanSpace ℝ (Fin k)) := a '' V
  have hTo : IsOpen T := φ.isOpen_image_of_subset_source hVo inter_subset_left
  let h : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m) := fun y => c' (f (φ.symm y))
  have hleft : ∀ x ∈ V, φ.symm (a x) = x := fun x hx => φ.left_inv hx.1
  have hhc : ContDiffOn ℝ 1 h T := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨ex, hex⟩ := hx.2.2
    have htgt : a x ∈ φ.target := φ.map_source hx.1
    have hder : HasFDerivAt φ (ex : E →L[ℝ] EuclideanSpace ℝ (Fin k)) (φ.symm (a x)) := by
      rw [hleft x hx, hex]
      exact had x (hVU hx)
    have hcd : ContDiffAt ℝ 1 φ (φ.symm (a x)) := by
      rw [hleft x hx]
      exact c.contDiff.contDiffAt.comp x (hfc x (hVU hx))
    have hψ := φ.contDiffAt_symm htgt hder hcd
    have hf' : ContDiffAt ℝ 1 f (φ.symm (a x)) := by
      rw [hleft x hx]
      exact hfc x (hVU hx)
    exact (c'.contDiff.contDiffAt.comp _ (hf'.comp _ hψ)).contDiffWithinAt
  have hQf : ∀ x ∈ V, Q (f x) = realGraphPt h (a x) := by
    intro x hx
    show pairPt (c (f x)) (c' (f x)) = pairPt (a x) (c' (f (φ.symm (a x))))
    rw [hleft x hx]

  have hJ : ∀ x ∈ V, areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F) =
      graphJac (fderiv ℝ h (a x) : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) *
        ((c.comp (fderiv ℝ f x) : E →L[ℝ] EuclideanSpace ℝ (Fin k)) :
          E →ₗ[ℝ] EuclideanSpace ℝ (Fin k)).normDet := by
    intro x hx
    have hhd : HasFDerivAt h (fderiv ℝ h (a x)) (a x) :=
      ((hhc.contDiffAt (hTo.mem_nhds ⟨x, hx, rfl⟩)).differentiableAt one_ne_zero).hasFDerivAt
    have h1 : HasFDerivAt (fun z => c' (f z)) (c'.comp (fderiv ℝ f x)) x :=
      c'.hasFDerivAt.comp x (hfd x (hVU hx))
    have h2 : HasFDerivAt (fun z => h (a z)) ((fderiv ℝ h (a x)).comp (c.comp (fderiv ℝ f x))) x :=
      hhd.comp x (had x (hVU hx))
    have heq : c'.comp (fderiv ℝ f x) = (fderiv ℝ h (a x)).comp (c.comp (fderiv ℝ f x)) :=
      h1.unique (h2.congr_of_eventuallyEq (Filter.eventually_of_mem (hVo.mem_nhds hx)
        fun z hz => by simp only [h, hleft z hz]))
    have hlin : Q ∘ₗ (fderiv ℝ f x : E →ₗ[ℝ] F) =
        graphLin (fderiv ℝ h (a x)) ∘ₗ ((c.comp (fderiv ℝ f x) : E →L[ℝ] EuclideanSpace ℝ (Fin k)) :
          E →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) := by
      refine LinearMap.ext fun v => ?_
      have hv := congrArg (fun M : E →L[ℝ] EuclideanSpace ℝ (Fin m) => M v) heq
      simp only [ContinuousLinearMap.comp_apply] at hv
      show pairPt (c (fderiv ℝ f x v)) (c' (fderiv ℝ f x v)) =
        pairPt (c (fderiv ℝ f x v)) (fderiv ℝ h (a x) (c (fderiv ℝ f x v)))
      rw [hv]
    rw [SheetImageAreaSet.areaJacobian_eq_normDet, ← normDet_comp_of_norm Q hQ, hlin,
      LinearMap.normDet_comp_of_finrank_eq _ _ hdim, normDet_graphLin]

  have hBV' : B ⊆ φ.source := fun x hx => (hBV hx).1
  have hinjB : InjOn a B := φ.injOn.mono hBV'
  have haB : MeasurableSet (a '' B) :=
    hB.image_of_continuousOn_injOn
      (fun x hx => (had x (hVU (hBV hx))).continuousAt.continuousWithinAt) hinjB
  have hBT : a '' B ⊆ T := image_mono hBV
  have hQi : Isometry Q := AddMonoidHomClass.isometry_of_norm Q hQ
  calc μH[(k : ℝ)] (f '' B) = μH[(k : ℝ)] (Q '' (f '' B)) :=
        (hQi.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg k)) _).symm
    _ = μH[(k : ℝ)] (realGraphPt h '' (a '' B)) := by
        rw [image_image, image_image]
        exact congrArg _ (image_congr fun x hx => hQf x (hBV hx))
    _ = ∫⁻ y in a '' B, ENNReal.ofReal (graphJac (fderiv ℝ h y :
          EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) ∂(μH[(k : ℝ)]) :=
        hAG k m T h hTo hhc (a '' B) hBT haB
    _ = ∫⁻ x in B, ENNReal.ofReal (graphJac (fderiv ℝ h (a x) :
          EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) *
          ENNReal.ofReal ((c.comp (fderiv ℝ f x) : E →L[ℝ] EuclideanSpace ℝ (Fin k)) :
            E →ₗ[ℝ] EuclideanSpace ℝ (Fin k)).normDet ∂(μH[(k : ℝ)]) :=
        setLIntegral_image hk hB (fun x hx => (had x (hVU (hBV hx))).hasFDerivWithinAt) hinjB _
    _ = _ := by
        refine setLIntegral_congr_fun hB fun x hx => ?_
        rw [hJ x (hBV hx), ENNReal.ofReal_mul (by unfold graphJac; exact Real.sqrt_nonneg _)]
end AreaFormulaLocal
end GroundTheory.Heights₂.Heights
