-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_exists_injective_67792887b40a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:56:47.19646+00:00
-- url     : https://prove2.me/submissions/9f8d8ac8-a857-4120-b7e5-b5367c690b1d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StCriticalFibreInfinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsSheetOnlyNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_smul_mem_fibre_ea8dfa373a59
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_differentiableAt_ratio_f91644499ea4
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
theorem _root_.solution (hC : CriticalFibreInfinite.Statement) {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ' : IsGoodProj P Ψ')
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {V : Set (Fin e → ℂ)} (hV : IsOpen V) (hVne : V.Nonempty)
    (hγ : ∀ y ∈ V, DifferentiableAt ℂ γ y ∧ γ y ∈ mcPts P ∧ Ψ (segre (γ y)) = Fin.cons 1 y)
    (h0 : ∀ y ∈ V, Ψ' (segre (γ y)) 0 ≠ 0) :
    ∃ y ∈ V, Function.Injective (fderiv ℂ (fun y' => ratio (Ψ' (segre (γ y')))) y) := by
  by_contra hall
  push Not at hall
  have : Nonempty K := hP.1
  obtain ⟨t, ht⟩ := hC e e V (fun y' => ratio (Ψ' (segre (γ y')))) hV hVne
    (fun y hy => (differentiableAt_ratio Ψ' (hγ y hy).1 (h0 y hy)).differentiableWithinAt) hall
  refine (fibreFinite K ι P e Ψ' hP hΨ' t).not_infinite ?_
  have hinj : Set.InjOn (fun y => (Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y))
      {y | y ∈ V ∧ ratio (Ψ' (segre (γ y))) = t} := by
    rintro y1 ⟨hy1, -⟩ y2 ⟨hy2, -⟩ h
    have h' := congrArg Ψ h
    simp only [map_smul, (hγ y1 hy1).2.2, (hγ y2 hy2).2.2] at h'
    have e0 := congrFun h' 0
    simp only [Pi.smul_apply, Fin.cons_zero, smul_eq_mul, mul_one] at e0
    funext i
    have ei := congrFun h' i.succ
    simp only [Pi.smul_apply, Fin.cons_succ, smul_eq_mul] at ei
    rw [e0] at ei
    exact mul_left_cancel₀ (inv_ne_zero (h0 y2 hy2)) ei
  refine (Set.Infinite.image hinj ht).mono ?_
  rintro _ ⟨y, ⟨hy, hty⟩, rfl⟩
  have := smul_mem_fibre hP.2.1.2.1 (hγ y hy).2.1 Ψ' (h0 y hy)
  rwa [hty] at this
end GroundTheory.Heights₂.Heights.PtsSheetOnlyNull
