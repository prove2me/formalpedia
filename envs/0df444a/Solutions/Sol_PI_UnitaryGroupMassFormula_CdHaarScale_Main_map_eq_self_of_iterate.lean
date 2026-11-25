-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CdHaarScale.Main.map_eq_self_of_iterate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:37:49.671273+00:00
-- url     : https://prove2.me/submissions/b0643ec7-af0c-4631-8283-3336054798f9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CdHaarScale
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarScaling_MapEqSelfOfIterate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CdHaarScale PI.UnitaryGroupMassFormula.CdHaarScale.Main
namespace PI.UnitaryGroupMassFormula.CdHaarScale.Main
theorem _root_.solution {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (ψ : G ≃ₜ* G) (N : ℕ) (hN : N ≠ 0)
    (hψ : ∀ x, ψ^[N] x = x) : μ.map ψ = μ := by
  have hm : Measurable ψ := ψ.continuous.measurable
  haveI : (μ.map ψ).IsHaarMeasure := inferInstance
  set c := (μ.map ψ).haarScalarFactor μ with hc
  have hμc : μ.map ψ = c • μ := isMulLeftInvariant_eq_smul _ _
  have hk : ∀ k : ℕ, μ.map (ψ^[k]) = c ^ k • μ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ', ← Measure.map_map hm (hm.iterate k), ih, Measure.map_smul, hμc,
        smul_smul, pow_succ]
  have hid : (⇑ψ)^[N] = id := funext hψ
  have hN' : μ = c ^ N • μ := by rw [← hk N, hid, Measure.map_id]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have h0 : μ K ≠ 0 := (measure_pos_of_mem_nhds μ hK1).ne'
  have htop : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have hKeq : ((c ^ N : NNReal) : ENNReal) * μ K = 1 * μ K := by
    have := congrArg (fun ν : Measure G => ν K) hN'
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
    rw [one_mul]
    exact this.symm
  have hcN : (c : ℝ) ^ N = 1 := by
    have h3 := congrArg ENNReal.toReal hKeq
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at h3
    have hpos : 0 < (μ K).toReal := ENNReal.toReal_pos h0 htop
    have h4 := mul_right_cancel₀ hpos.ne' h3
    simpa using h4
  have hc1 : c = 1 := by
    have := (pow_eq_one_iff_of_nonneg c.2 hN).1 hcN
    exact NNReal.eq (this.trans NNReal.coe_one.symm)
  rw [hμc, hc1, one_smul]
end PI.UnitaryGroupMassFormula.CdHaarScale.Main
