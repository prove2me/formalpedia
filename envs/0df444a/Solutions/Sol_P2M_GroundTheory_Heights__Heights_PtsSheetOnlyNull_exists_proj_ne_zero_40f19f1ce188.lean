-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_exists_proj_ne_zero_40f19f1ce188
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:26:18.437993+00:00
-- url     : https://prove2.me/submissions/d8e7e78c-d1ef-41d0-b8af-18a9a9c256db

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StCriticalFibreInfinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsSheetOnlyNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_differentiableAt_proj_segre_36c3e8284232
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_differentiableAt_ratio_f91644499ea4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_swapProj_apply_8d95c3de703d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_isGoodProj_swapProj_d961239fc7c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_not_injective_of_coord_eventually_const_10457ccc6c95
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_exists_injective_67792887b40a
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
theorem _root_.solution (hC : CriticalFibreInfinite.Statement) {P : Ideal (MRing ι)}
    (hP : IsArithVar P (e + 1)) {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ' : IsGoodProj P Ψ')
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {V : Set (Fin e → ℂ)} (hV : IsOpen V)
    (hγ : ∀ y ∈ V, DifferentiableAt ℂ γ y ∧ γ y ∈ mcPts P ∧ Ψ (segre (γ y)) = Fin.cons 1 y)
    {y : Fin e → ℂ} (hy : y ∈ V) : ∃ y' ∈ V, Ψ' (segre (γ y')) 0 ≠ 0 := by
  by_contra hall
  push Not at hall
  have hne : Ψ' (segre (γ y)) ≠ 0 := hΨ' _ (hγ y hy).2.1
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hj (hall y hy)
  have hcont : ContinuousOn (fun y' => Ψ' (segre (γ y')) j) V := fun y' hy' =>
    (differentiableAt_pi.1 (differentiableAt_proj_segre Ψ' (hγ y' hy').1) j).continuousAt.continuousWithinAt
  have hV'o : IsOpen (V ∩ (fun y' => Ψ' (segre (γ y')) j) ⁻¹' {0}ᶜ) :=
    hcont.isOpen_inter_preimage hV isOpen_compl_singleton
  have h0' : ∀ y' ∈ V ∩ (fun y' => Ψ' (segre (γ y')) j) ⁻¹' {0}ᶜ, swapProj j Ψ' (segre (γ y')) 0 ≠ 0 := by
    intro y' hy'
    simpa [swapProj_apply] using hy'.2
  obtain ⟨y1, hy1, hinj⟩ := exists_injective hC hP (isGoodProj_swapProj hΨ' j) hV'o ⟨y, hy, hj⟩
    (fun y' hy' => hγ y' hy'.1) h0'
  refine not_injective_of_coord_eventually_const (j.pred hj0) 0
    (differentiableAt_ratio _ (hγ y1 hy1.1).1 (h0' y1 hy1)) ?_ hinj
  filter_upwards [hV'o.mem_nhds hy1] with y' hy'
  simp [ratio, swapProj_apply, hall y' hy'.1]
end GroundTheory.Heights₂.Heights.PtsSheetOnlyNull
