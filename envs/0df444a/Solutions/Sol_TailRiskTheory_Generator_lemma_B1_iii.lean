-- Prove2me | solution 1 for TailRiskTheory.Generator.lemma_B1_iii
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T00:24:12.832516+00:00
-- url     : https://prove2.me/submissions/06eed02f-85c7-400d-8b6b-3693f1c57cde

import Mathlib
import Definitions.Def_TailRiskTheory_Generator_Model
import Definitions.Def_StochasticOrders_Usual_UsualOrder
import Theorems.Thm_StochasticOrders_Usual_usual_order_coupling_iff_v2

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open TailRiskSharing.VaRConv (distFn IsAtomless)
open TailRiskSharing.TailConv (Linf)
open TailRiskTheory.Generator

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : IsAtomless P) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (X Z : Ω → ℝ) (hX : X ∈ Linf P) (hZ : Z ∈ Linf P) (hXZ : IsPTailOf P p X Z) :
    StOrder P X Z := by
  have hXm : Measurable X := hX.1
  have hZm : Measurable Z := hZ.1
  have hp1' : (0 : ℝ) < 1 - p := by linarith
  -- the CDF of the tail lies below the CDF of X
  have hF : ∀ x, distFn P Z x ≤ distFn P X x := by
    intro x
    rw [hXZ x]
    unfold tailDistFn
    have hu0 : 0 ≤ distFn P X x := measureReal_nonneg
    have hu1 : distFn P X x ≤ 1 := by
      unfold distFn Measure.real
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
    rw [div_le_iff₀ hp1']
    apply max_le
    · nlinarith
    · nlinarith
  -- usual stochastic order
  have hcompl : ∀ (Y : Ω → ℝ), Measurable Y → ∀ x, P {ω | x < Y ω} = 1 - P {ω | Y ω ≤ x} := by
    intro Y hY x
    rw [← prob_compl_eq_one_sub (measurableSet_le hY measurable_const)]
    congr 1
    ext ω
    simp [not_le]
  have hUO : StochasticOrders.Usual.UsualOrder P P X Z := by
    intro x
    rw [hcompl X hXm x, hcompl Z hZm x]
    apply tsub_le_tsub_left
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp (hF x)
  obtain ⟨Ω'', mΩ, ρ, hρ, Xh, Zh, hXhm, hZhm, hXid, hZid, hle⟩ :=
    (StochasticOrders.Usual.usual_order_coupling_iff_v2 P P X Z hXm hZm).mp hUO
  intro f hf hfX hfZ
  have hfm : Measurable f := hf.measurable
  have e1 : ∫ ω, f (X ω) ∂P = ∫ ω, f (Xh ω) ∂ρ :=
    (hXid.comp hfm).integral_eq.symm
  have e2 : ∫ ω, f (Z ω) ∂P = ∫ ω, f (Zh ω) ∂ρ :=
    (hZid.comp hfm).integral_eq.symm
  have i1 : Integrable (fun ω => f (Xh ω)) ρ := ((hXid.comp hfm).integrable_iff).mpr hfX
  have i2 : Integrable (fun ω => f (Zh ω)) ρ := ((hZid.comp hfm).integrable_iff).mpr hfZ
  have hae : ∀ᵐ ω ∂ρ, Xh ω ≤ Zh ω := by
    rw [ae_iff]
    have hmeas : MeasurableSet {ω | Xh ω ≤ Zh ω} := measurableSet_le hXhm hZhm
    have := (prob_compl_eq_zero_iff hmeas).mpr hle
    simpa [Set.compl_def] using this
  rw [e1, e2]
  exact integral_mono_ae i1 i2 (hae.mono fun ω h => hf h)
