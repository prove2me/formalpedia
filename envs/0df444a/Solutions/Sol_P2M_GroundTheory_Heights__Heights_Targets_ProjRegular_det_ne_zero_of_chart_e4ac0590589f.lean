-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_det_ne_zero_of_chart_e4ac0590589f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:52.267709+00:00
-- url     : https://prove2.me/submissions/1cd268b3-b71b-44be-b064-66fac834cead

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_analyticAt_chart_4620b31d9b76

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.Targets.ProjRegular
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
namespace GroundTheory.Heights₂.Heights.Targets.ProjRegular
theorem _root_.solution {V : Set R.X} {BV : FinHolAtlas n V}
    (hB : HoloMap BV R.A Subtype.val) (y : V) (h0 : Ψ (segre (R.lift y.1 y.1)) 0 ≠ 0)
    {j k : Fin BV.n} (hj : y ∈ (BV.chart j).source) (hk : y ∈ (BV.chart k).source)
    (hd : LinearMap.det (fderiv ℂ ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart k).symm)
      (BV.chart k y) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0) :
    LinearMap.det (fderiv ℂ ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart j).symm)
      (BV.chart j y) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0 := by
  have hu0 : BV.chart j y ∈ (BV.chart j).target := (BV.chart j).map_source hj
  have hv0 : BV.chart k y ∈ (BV.chart k).target := (BV.chart k).map_source hk
  have hsj : (BV.chart j).symm (BV.chart j y) = y := (BV.chart j).left_inv hj
  have hsk : (BV.chart k).symm (BV.chart k y) = y := (BV.chart k).left_inv hk
  have hτu : (BV.chart k ∘ (BV.chart j).symm) (BV.chart j y) = BV.chart k y := by simp [hsj]
  have hτ : AnalyticAt ℂ (BV.chart k ∘ (BV.chart j).symm) (BV.chart j y) :=
    BV.holo j k _ ⟨hu0, by
      show (BV.chart j).symm (BV.chart j y) ∈ (BV.chart k).source; rw [hsj]; exact hk⟩
  have hσ : AnalyticAt ℂ (BV.chart j ∘ (BV.chart k).symm)
      ((BV.chart k ∘ (BV.chart j).symm) (BV.chart j y)) := by
    rw [hτu]
    exact BV.holo k j _ ⟨hv0, by
      show (BV.chart k).symm (BV.chart k y) ∈ (BV.chart j).source; rw [hsk]; exact hj⟩
  have hev : ∀ᶠ u in 𝓝 (BV.chart j y), (BV.chart j).symm u ∈ (BV.chart k).source :=
    ((BV.chart j).continuousAt_symm hu0).preimage_mem_nhds (by
      show (BV.chart k).source ∈ 𝓝 ((BV.chart j).symm (BV.chart j y))
      rw [hsj]; exact (BV.chart k).open_source.mem_nhds hk)
  have hid : (BV.chart j ∘ (BV.chart k).symm) ∘ (BV.chart k ∘ (BV.chart j).symm)
      =ᶠ[𝓝 (BV.chart j y)] id := by
    filter_upwards [hev, (BV.chart j).open_target.mem_nhds hu0] with u hu hut
    simp [(BV.chart k).left_inv hu, (BV.chart j).right_inv hut]
  have hq : (projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart j).symm =ᶠ[𝓝 (BV.chart j y)]
      ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart k).symm) ∘ (BV.chart k ∘ (BV.chart j).symm) := by
    filter_upwards [hev] with u hu
    simp [(BV.chart k).left_inv hu]
  have hqk : DifferentiableAt ℂ ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart k).symm)
      ((BV.chart k ∘ (BV.chart j).symm) (BV.chart j y)) := by
    rw [hτu]; exact (analyticAt_chart Ψ hB y h0 k hk).differentiableAt
  have hinv : (fderiv ℂ (BV.chart j ∘ (BV.chart k).symm)
      ((BV.chart k ∘ (BV.chart j).symm) (BV.chart j y))).comp
      (fderiv ℂ (BV.chart k ∘ (BV.chart j).symm) (BV.chart j y)) =
      ContinuousLinearMap.id ℂ (Fin n → ℂ) := by
    rw [← fderiv_comp _ hσ.differentiableAt hτ.differentiableAt, hid.fderiv_eq, fderiv_id]
  have hdetτ : LinearMap.det (fderiv ℂ (BV.chart k ∘ (BV.chart j).symm) (BV.chart j y) :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0 := by
    intro h
    have := congrArg (fun f : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) =>
      LinearMap.det (f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) hinv
    simp [LinearMap.det_comp, h] at this
  rw [hq.fderiv_eq, fderiv_comp _ hqk hτ.differentiableAt, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.det_comp, hτu]
  exact mul_ne_zero hd hdetτ
end GroundTheory.Heights₂.Heights.Targets.ProjRegular
