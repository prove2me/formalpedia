-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_ptsIntegralAt_eq_75a87a6f567f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:08:49.386577+00:00
-- url     : https://prove2.me/submissions/da078f2a-1f59-41e4-8bf2-4754306a345b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassGeomDegChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassLeRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassGeomDegChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_fin_one_fun_eq_const_141b478a75fe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_mem_mcPts_9510ee445b9b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_apply_eq_segre_ad27c26f28d4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_segre_blockLift_a51900c6d6c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_card_seg_fc6c01e0c149
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_injective_of_good_3f4a3c80eead
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_cxHessian_congr


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
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
theorem _root_.solution {Ψ : (((k : Fin 1) → plBlocks 1 1 n k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)}
    (hΨ : IsGoodProj (grassIdeal 1 1 n) Ψ) :
    ∃ B : Matrix (PlIdx 1 n) (Fin (n + 1)) ℂ, Function.Bijective B.mulVec ∧
      ptsIntegralAt (grassIdeal 1 1 n) Ψ (fun _ z => Real.log ((fsMulti (plBlocks 1 1 n)).h z)) (fun _ => 1) =
        chartMass (Bᴴ * B) := by
  have hinj := injective_of_good hΨ
  have hrank : Module.finrank ℂ ((Fin 1 → PlIdx 1 n) → ℂ) = Module.finrank ℂ (Fin (n + 1) → ℂ) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, card_seg, Fintype.card_fin]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
  set L := (LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm with hL
  have hΨL : ∀ v, Ψ (L v) = v := (LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).apply_symm_apply
  have hLΨ : ∀ w, L (Ψ w) = w := (LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm_apply_apply
  set M := L.trans (LinearEquiv.funCongrLeft ℂ ℂ (Equiv.funUnique (Fin 1) (PlIdx 1 n))).symm with hM
  set B := LinearMap.toMatrix' M.toLinearMap with hB
  have hmv : ∀ v, B *ᵥ v = M v := fun v => LinearMap.toMatrix'_mulVec _ _
  have hMapp : ∀ v I, M v I = L v fun _ => I := fun v I => rfl
  refine ⟨B, ?_, ?_⟩
  · convert M.bijective using 1
    funext v
    exact hmv v
  have hseg : ∀ v, segre (ι := plBlocks 1 1 n) (blockLift (M v)) = L v := by
    intro v
    rw [segre_blockLift]
    funext i
    rw [hMapp, fin_one_fun_eq_const]
  have hMdiff : Differentiable ℂ fun v => M v := (LinearMap.toContinuousLinearMap M.toLinearMap).differentiable
  have hcons : Differentiable ℂ fun y' : Fin n → ℂ => (Fin.cons 1 y' : Fin (n + 1) → ℂ) := by
    rw [differentiable_pi]
    intro c
    refine Fin.cases ?_ (fun i => ?_) c
    · simp only [Fin.cons_zero]
      exact differentiable_const _
    · simp only [Fin.cons_succ]
      exact differentiable_apply i
  set γ0 : (Fin n → ℂ) → (Σ _ : Fin 1, PlIdx 1 n) → ℂ := fun y' => blockLift (M (Fin.cons 1 y')) with hγ0
  have hγ0d : ∀ y', DifferentiableAt ℂ γ0 y' := by
    intro y'
    rw [differentiableAt_pi]
    intro p
    exact ((differentiable_apply p.2).comp (hMdiff.comp hcons)) y'
  have hγ0mem : ∀ y', γ0 y' ∈ mcPts (grassIdeal 1 1 n) := by
    intro y'
    have hv : (Fin.cons 1 y' : Fin (n + 1) → ℂ) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
    obtain ⟨I, hI⟩ := Function.ne_iff.mp ((M.map_ne_zero_iff).mpr hv)
    exact (mem_mcPts _).2 fun _ => ⟨I, hI⟩
  have hpot : ∀ y', Real.log ((fsMulti (plBlocks 1 1 n)).h (γ0 y')) = hermChartPot (Bᴴ * B) y' := by
    intro y'
    set v : Fin (n + 1) → ℂ := Fin.cons 1 y'
    have h1 : (fsMulti (plBlocks 1 1 n)).h (γ0 y') = ‖WithLp.toLp 2 (B *ᵥ v)‖ := by
      rw [hmv]
      simp [fsMulti, HermLine.ofMetrics, fsMetric, hγ0, blockLift, v]
    have h2 : (star v ⬝ᵥ ((Bᴴ * B) *ᵥ v)).re = ∑ I, ‖(B *ᵥ v) I‖ ^ 2 := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
      simp [dotProduct, Complex.re_sum, Complex.conj_mul']
      norm_cast
    rw [hermChartPot, h1, h2, EuclideanSpace.norm_eq]
  unfold ptsIntegralAt chartMass
  congr 1
  funext y
  have hfib : fibre (grassIdeal 1 1 n) Ψ y = {L (Fin.cons 1 y)} := by
    ext w
    simp only [fibre, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, -, -, hw⟩
      rw [← hw, hLΨ]
    · rintro rfl
      exact ⟨γ0 y, hγ0mem y, hseg _, hΨL _⟩
  have hsheet : IsSheet (grassIdeal 1 1 n) Ψ y (L (Fin.cons 1 y)) γ0 :=
    ⟨hseg _, Eventually.of_forall fun y' => ⟨hγ0d y', hγ0mem y', by rw [hseg, hΨL]⟩⟩
  rw [hfib, finsum_mem_singleton]
  unfold sheetDensity
  split_ifs with hγ
  · have hev : (fun y' => Real.log ((fsMulti (plBlocks 1 1 n)).h (hγ.choose y'))) =ᶠ[𝓝 y]
        hermChartPot (Bᴴ * B) := by
      filter_upwards [hγ.choose_spec.2] with y' hy'
      have hs : segre (ι := plBlocks 1 1 n) (hγ.choose y') = segre (ι := plBlocks 1 1 n) (γ0 y') := by
        rw [hseg, ← hy'.2.2, hLΨ]
      have he : hγ.choose y' = γ0 y' := by
        funext p
        rw [apply_eq_segre (hγ.choose y') p, apply_eq_segre (γ0 y') p, hs]
      rw [he, hpot]
    simp only [one_mul, maDensity, cxHessian_congr hev]
  · exact absurd ⟨γ0, hsheet⟩ hγ
end GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
