-- Prove2me | solution 1 for OTSensitivity.Consist.eq_80
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:24:05.188992+00:00
-- url     : https://prove2.me/submissions/b80c8b0c-38d7-4f98-8d2f-ba1f1ef5a91e

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_Consist_Setting
import Definitions.Def_OTSensitivity_Consist_Estimation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

open OTSensitivity.Consist in
theorem solution {𝒳 𝒴 : Type*}
    [Fintype 𝒳] [TopologicalSpace 𝒳] [DiscreteTopology 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k)
    (π : Measure (𝒳 × 𝒴)) [IsProbabilityMeasure π] (κ : Kernel 𝒳 𝒴)
    (hκ : IsCondDistrib π Prod.fst Prod.snd ‹MeasurableSpace 𝒳› κ) :
    xi k π Prod.fst Prod.snd κ =
      ∑ x ∈ Finset.univ.filter (fun x => π.fst {x} ≠ 0),
        π.fst {x} * RWPI.SqrtLasso.transportCost k π.snd (cellLaw π {x}) := by
  have hfst : π.map Prod.fst = π.fst := rfl
  have hsnd : π.map Prod.snd = π.snd := rfl
  have hcell : ∀ x, π.fst {x} ≠ 0 → κ x = cellLaw π {x} := by
    intro x hx
    ext B hB
    have key := hκ.2.2 {x} (measurableSet_singleton x) B hB
    rw [lintegral_singleton, hfst] at key
    unfold cellLaw
    rw [Measure.smul_apply, Measure.snd_apply hB,
      Measure.restrict_apply (hB.preimage measurable_snd), Set.prod_univ, Set.inter_comm, key,
      smul_eq_mul, mul_comm (κ x B), ← mul_assoc,
      ENNReal.inv_mul_cancel hx (measure_ne_top _ _), one_mul]
  unfold xi
  rw [hfst, hsnd, lintegral_fintype, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with hx
  · rw [mul_comm, hcell x hx]
  · push Not at hx
    rw [hx, mul_zero]
