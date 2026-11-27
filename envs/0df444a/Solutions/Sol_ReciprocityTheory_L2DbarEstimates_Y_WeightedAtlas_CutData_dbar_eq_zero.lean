-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.CutData.dbar_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:31:10.931313+00:00
-- url     : https://prove2.me/submissions/3ca79fb6-02c3-49f6-b8bb-7b911eb320a6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxJ
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxK
import Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData_eventually___one_ae6e010d4c36
import Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData_eventually___zero_71899b15eb44
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData_K_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_dbarAt_eq_zero_of_holo
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_isOpen_ovl
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_mem_ovl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex Metric Set
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  {A : WeightedAtlas n Y ι La}
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.CutData
variable {Sf : Finset Y} (D : CutData A Sf)
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.CutData
theorem _root_.solution (la' : La) (c : Y → ℂ) (j : ι) {y : Y} (hj : y ∈ (A.chart j).source)
    (hT : y ∉ ⋃ P ∈ Sf, D.T P) (ξ : Fin n → ℂ) :
    A.dbarAt j (A.F0 la' Sf A.pick D.χ c) y ξ = 0 := by
  classical
  set G : V n → ℂ := fun v => ∑ P ∈ Sf,
    (if y ∈ D.K P then c P * A.g la' j (A.pick P) ((A.chart j).symm v) else 0)
  have hloc : ∀ P ∈ Sf, ∀ᶠ v in 𝓝 (A.chart j y),
      c P * (D.χ P ((A.chart j).symm v) : ℂ) * A.g la' j (A.pick P) ((A.chart j).symm v) =
        (if y ∈ D.K P then c P * A.g la' j (A.pick P) ((A.chart j).symm v) else 0) := by
    intro P hP
    by_cases hK : y ∈ D.K P
    · obtain ⟨u, hu2, rfl⟩ := hK
      have hu1 : u ∈ ball (A.chart (A.pick P) P) (D.r1 P) := by
        by_contra h
        exact hT (mem_biUnion hP ⟨u, ⟨hu2, h⟩, rfl⟩)
      have huT := (D.sub P hP hu2).1
      have hyP : (A.chart (A.pick P)).symm u ∈ (A.chart (A.pick P)).source :=
        (A.chart (A.pick P)).map_target huT
      have hb : A.chart (A.pick P) ((A.chart (A.pick P)).symm u) ∈
          ball (A.chart (A.pick P) P) (D.r1 P) := by rwa [(A.chart (A.pick P)).right_inv huT]
      filter_upwards [D.eventually_χ_one j hj hyP hb] with v hv
      rw [if_pos ⟨u, hu2, rfl⟩, hv.2]; simp
    · filter_upwards [D.eventually_χ_zero hP j hj hK] with v hv
      rw [if_neg hK, hv]; simp
  have hev : (A.F0 la' Sf A.pick D.χ c j ∘ (A.chart j).symm) =ᶠ[𝓝 (A.chart j y)] G := by
    filter_upwards [(Filter.eventually_all_finset Sf).2 hloc] with v hv
    exact Finset.sum_congr rfl hv
  refine A.dbarAt_eq_zero_of_holo j _ y hev ?_ ξ
  refine DifferentiableAt.fun_sum fun P hP => ?_
  by_cases hK : y ∈ D.K P
  · simp only [if_pos hK]
    have hyP := ((D.K_sub hP) hK).1
    exact ((A.holo_g la' j (A.pick P)).differentiableAt
      ((A.isOpen_ovl j _).mem_nhds (A.mem_ovl hj hyP))).const_mul _
  · simp only [if_neg hK]; exact differentiableAt_const _
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.CutData
