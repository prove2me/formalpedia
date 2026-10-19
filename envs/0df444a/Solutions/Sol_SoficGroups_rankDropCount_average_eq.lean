-- Prove2me | solution 1 for SoficGroups.rankDropCount_average_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/8246a69c-7dff-4611-a456-f190a9761183

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_rankDropCount_integral_eq

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (H : ℝ) (hH : 0 < H) :
    MeasureTheory.average
        (MeasureTheory.volume.restrict (Set.Ico 0 H))
        (fun r : ℝ => rankDropCount u v H r) =
      H⁻¹ * ∑ i : ι,
        (MeasureTheory.volume.restrict (Set.Ico 0 H)).real
          {r : ℝ | ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋} := by
  rw [MeasureTheory.average_eq,
    MeasureTheory.measureReal_restrict_apply_univ,
    Real.volume_real_Ico_of_le hH.le, sub_zero,
    rankDropCount_integral_eq]
  exact smul_eq_mul _ _
end SoficGroups
