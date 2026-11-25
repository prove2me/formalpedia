-- Prove2me | solution 1 for PI.VolStabS.cosDens_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:49.393167+00:00
-- url     : https://prove2.me/submissions/fdca2d3f-d942-49e1-9508-bd813bd140fc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_CosDens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_MeasureEqOfCos
import Theorems.Thm_PI_VolStabS_measure_eq_of_cos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open MeasureTheory Topology Set Filter
namespace PI.VolStabS
theorem _root_.solution : CosDens := by
  unfold CosDens
  intro X _ _ _ _ _ _ ν m _ _ H hHo _ hanti hb c0 κ hm0 hcos S hS
  have hle : ∀ n, H n ≤ H 0 := fun n => hanti (Nat.zero_le n)
  have hcos' : ∀ n y, m {z | z - y ∈ H n} = ((κ • ν).restrict {z | z - c0 ∈ H 0}) {z | z - y ∈ H n} := by
    intro n y
    have hmeas : MeasurableSet {z : X | z - y ∈ H n} :=
      ((hHo n).preimage (continuous_id.sub continuous_const)).measurableSet
    rw [Measure.restrict_apply hmeas, Measure.smul_apply, smul_eq_mul]
    by_cases hy : y - c0 ∈ H 0
    · have hsub : {z : X | z - y ∈ H n} ∩ {z | z - c0 ∈ H 0} = {z | z - y ∈ H n} := by
        apply inter_eq_left.mpr
        intro z hz
        have e : z - c0 = (z - y) + (y - c0) := by abel
        show z - c0 ∈ H 0
        rw [e]
        exact (H 0).add_mem (hle n hz) hy
      rw [hsub]
      exact hcos n y hy
    ·
      have hout : ∀ z, z - y ∈ H n → z - c0 ∉ H 0 := by
        intro z hz hz0
        apply hy
        have e : y - c0 = (z - c0) - (z - y) := by abel
        rw [e]
        exact (H 0).sub_mem hz0 (hle n hz)
      have hempty : {z : X | z - y ∈ H n} ∩ {z | z - c0 ∈ H 0} = ∅ := by
        ext z
        simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact hout z
      rw [hempty, measure_empty, mul_zero]
      exact measure_mono_null (fun z hz => hout z hz) hm0
  rw [measure_eq_of_cos m _ H hHo hanti hb hcos' S hS hS.isClosed,
    Measure.restrict_apply hS.isClosed.measurableSet, Measure.smul_apply, smul_eq_mul]
end PI.VolStabS
