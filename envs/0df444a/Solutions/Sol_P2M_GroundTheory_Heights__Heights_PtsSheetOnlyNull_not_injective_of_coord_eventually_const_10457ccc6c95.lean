-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_not_injective_of_coord_eventually_const_10457ccc6c95
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:55:50.526504+00:00
-- url     : https://prove2.me/submissions/12c10ca2-6acb-4441-b09f-ed99efd5bc4b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StCriticalFibreInfinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsSheetOnlyNull
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood
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
theorem _root_.solution {f : (Fin e → ℂ) → Fin e → ℂ} {y : Fin e → ℂ} (m : Fin e) (c : ℂ)
    (hf : DifferentiableAt ℂ f y) (hc : ∀ᶠ y' in 𝓝 y, f y' m = c) : ¬ Function.Injective (fderiv ℂ f y) := by
  intro hinj
  have h1 : HasFDerivAt (fun y' => f y' m) ((ContinuousLinearMap.proj m).comp (fderiv ℂ f y)) y :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) m).hasFDerivAt.comp y hf.hasFDerivAt
  have h2 : HasFDerivAt (fun y' => f y' m) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const c y).congr_of_eventuallyEq hc
  have h3 := h1.unique h2
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective
    (f := (fderiv ℂ f y : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)))).1 hinj (Pi.single m 1)
  have h4 := congrArg (fun L : (Fin e → ℂ) →L[ℂ] ℂ => L v) h3
  have h5 : fderiv ℂ f y v m = 1 := by simpa using congrFun hv m
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.zero_apply, h5] at h4
  exact one_ne_zero h4
end GroundTheory.Heights₂.Heights.PtsSheetOnlyNull
