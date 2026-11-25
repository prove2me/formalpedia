-- Prove2me | solution 1 for PI.VolStabW.cosDens_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:25:05.423902+00:00
-- url     : https://prove2.me/submissions/76e9e74a-e1a7-4024-bf3b-d3ff6917fbdb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_CosDens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_MeasureEqOfCos
import Theorems.Thm_PI_VolStabW_measure_eq_of_cos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Topology Set Filter
namespace PI.VolStabW
theorem _root_.solution : CosDens := by
  intro X _ _ _ _ _ _ ν m _ _ H hHo _ hHa hb c0 κ hCc hcos S hS
  set C : Set X := {z | z - c0 ∈ H 0} with hC
  have hCm : MeasurableSet C :=
    ((hHo 0).preimage (continuous_id.sub continuous_const)).measurableSet
  have key : ∀ n y, m {z | z - y ∈ H n} = (κ • ν.restrict C) {z | z - y ∈ H n} := by
    intro n y
    rw [Measure.smul_apply, Measure.restrict_apply' hCm, smul_eq_mul]
    by_cases hy : y - c0 ∈ H 0
    · have hsub : {z | z - y ∈ H n} ⊆ C := by
        intro z hz
        have := (H 0).add_mem (hHa (Nat.zero_le n) hz) hy
        simpa [hC, sub_add_sub_cancel] using this
      rw [Set.inter_eq_left.2 hsub]
      exact hcos n y hy
    · have hdis : {z | z - y ∈ H n} ∩ C = ∅ := by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hC, Set.mem_empty_iff_false, iff_false,
          not_and]
        intro hz hzc
        apply hy
        have := (H 0).sub_mem hzc (hHa (Nat.zero_le n) hz)
        simpa [sub_sub_sub_cancel_left] using this
      rw [hdis, measure_empty, mul_zero]
      refine measure_mono_null (fun z hz => ?_) hCc
      intro hzc
      apply hy
      have := (H 0).sub_mem hzc (hHa (Nat.zero_le n) hz)
      simpa [sub_sub_sub_cancel_left] using this
  have := measure_eq_of_cos m (κ • ν.restrict C) H hHo hHa hb key S hS hS.isClosed
  rw [this, Measure.smul_apply, Measure.restrict_apply' hCm, smul_eq_mul]
end PI.VolStabW
