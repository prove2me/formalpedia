-- Prove2me | solution 1 for PIW.HCFdeg.modChar_eq_one_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:26:23.66424+00:00
-- url     : https://prove2.me/submissions/241b039f-2e4b-4d0f-bfae-72c91b72efa0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Unimod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open MeasureTheory PI.UpqRep Matrix
open scoped MatrixOrder NNReal ENNReal ComplexOrder Pointwise
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace PIW.HCFdeg
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] [μ.InnerRegular]
    (K : Subgroup G) (hK : IsCompact (K : Set G)) (k : G) (hk : k ∈ K) :
    Measure.modularCharacter k = 1 := by
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : G)
  set E : Set G := V * (K : Set G) with hE
  have hEc : IsCompact E := hVc.mul hK
  have hVE : V ⊆ E := fun v hv => ⟨v, hv, 1, K.one_mem, mul_one v⟩
  have hEn : E ∈ nhds (1 : G) := Filter.mem_of_superset hV1 hVE
  have hpos : 0 < μ E := Measure.measure_pos_of_mem_nhds μ hEn
  have hfin : μ E ≠ ⊤ := hEc.measure_lt_top.ne
  have hpre : (fun x => x * k) ⁻¹' E = E := by
    ext x
    simp only [Set.mem_preimage, hE, Set.mem_mul]
    constructor
    · rintro ⟨v, hv, c, hc, hvc⟩
      refine ⟨v, hv, c * k⁻¹, K.mul_mem hc (K.inv_mem hk), ?_⟩
      rw [← mul_assoc, hvc, mul_inv_cancel_right]
    · rintro ⟨v, hv, c, hc, rfl⟩
      exact ⟨v, hv, c * k, K.mul_mem hc hk, (mul_assoc _ _ _).symm⟩
  have h := Measure.map_right_mul_eq_modularCharacterFun_smul μ k
  have h2 := congrArg (fun ν : Measure G => ν E) h
  rw [Measure.map_apply (measurable_mul_const k) hEc.isClosed.measurableSet, hpre,
    Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  have h3 : ((Measure.modularCharacterFun k : ℝ≥0) : ℝ≥0∞) * μ E = 1 * μ E := by
    rw [one_mul]; exact h2.symm
  have h4 := (ENNReal.mul_left_inj hpos.ne' hfin).1 h3
  exact_mod_cast h4
end PIW.HCFdeg
