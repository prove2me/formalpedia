-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fn_mem_Mset_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:09:49.495488+00:00
-- url     : https://prove2.me/submissions/16e1f6a0-7a33-4dc4-b229-20c25bd884ec

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ImportsAlt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_hom_of_ne
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_hom_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_denominator_ne_zero_pick_iff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_zmap_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.L2DbarEstimates.Y.fn_hom_zero

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Set
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) {i : ι} {y : Y} (hy : y ∈ (A.chart i).source) :
    y ∈ A.Mset w0 s De ↔ fnHom De (w0 i y) (fun k => s k i y) ≠ 0 := by
  by_cases h0 : w0 i y = 0
  · rw [h0, fn_hom_zero]
    constructor
    · intro hm
      obtain ⟨h1, -⟩ := hm
      exact absurd ((denominator_ne_zero_pick_iff A hD hy).1 h1) (by simp [h0])
    · intro h
      exact absurd rfl h
  · rw [fn_hom_of_ne De h0]
    have hz := fn_zmap_eq A hD hy
    simp only [Mset, Set.mem_setOf_eq, hz]
    constructor
    · rintro ⟨-, h2⟩
      exact mul_ne_zero (pow_ne_zero _ h0) (by simpa using h2)
    · intro h2
      exact ⟨(denominator_ne_zero_pick_iff A hD hy).2 h0, by simpa using right_ne_zero_of_mul h2⟩
end ReciprocityTheory.L2DbarEstimates.Y
