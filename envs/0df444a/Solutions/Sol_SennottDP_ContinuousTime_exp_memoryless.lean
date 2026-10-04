-- Prove2me | solution 1 for SennottDP.ContinuousTime.exp_memoryless
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T17:52:55.52547+00:00
-- url     : https://prove2.me/submissions/c16749e7-a0f6-4c0a-abab-bba31cc0157d

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

namespace CE904F8A

lemma tail {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (μ : ℝ) (hμ : 0 < μ) (hX : Measurable X) (hlaw : P.map X = expMeasure μ)
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | t < X ω} = ENNReal.ofReal (Real.exp (-(μ * t))) := by
  have := isProbabilityMeasure_expMeasure hμ
  have h1 : P {ω | t < X ω} = expMeasure μ (Set.Ioi t) := by
    rw [← hlaw, Measure.map_apply hX measurableSet_Ioi]; rfl
  have h2 : (expMeasure μ).real (Set.Ioi t) = Real.exp (-(μ * t)) := by
    have hc : (Set.Iic t)ᶜ = Set.Ioi t := Set.compl_Iic
    rw [← hc, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real,
      cdf_expMeasure_eq hμ, if_pos ht]
    ring
  rw [h1, ← h2, ofReal_measureReal]

lemma cdfP {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (μ : ℝ) (hμ : 0 < μ) (hX : Measurable X) (hlaw : P.map X = expMeasure μ)
    (t : ℝ) (ht : 0 ≤ t) :
    (P {ω | X ω ≤ t}).toReal = 1 - Real.exp (-(μ * t)) := by
  have := isProbabilityMeasure_expMeasure hμ
  have h1 : P {ω | X ω ≤ t} = expMeasure μ (Set.Iic t) := by
    rw [← hlaw, Measure.map_apply hX measurableSet_Iic]; rfl
  rw [h1, ← measureReal_def, ← cdf_eq_real, cdf_expMeasure_eq hμ, if_pos ht]

end CE904F8A

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics in
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (μ : ℝ) (hμ : 0 < μ) (hX : Measurable X) (hlaw : P.map X = expMeasure μ) :
    (∀ x y : ℝ, 0 < x → 0 < y →
        P[|{ω | y < X ω}] {ω | x + y < X ω} = P {ω | x < X ω}) ∧
      (fun δ : ℝ => (P {ω | X ω ≤ δ}).toReal - μ * δ) =o[𝓝[>] (0 : ℝ)] (fun δ : ℝ => δ) := by
  constructor
  · intro x y hx hy
    have hmeas : MeasurableSet {ω | y < X ω} := measurableSet_lt measurable_const hX
    rw [cond_apply hmeas]
    have hsub : {ω | y < X ω} ∩ {ω | x + y < X ω} = {ω | x + y < X ω} := by
      ext ω; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨by linarith, h⟩
    rw [hsub, CE904F8A.tail P X μ hμ hX hlaw y hy.le,
      CE904F8A.tail P X μ hμ hX hlaw (x + y) (by linarith),
      CE904F8A.tail P X μ hμ hX hlaw x hx.le]
    have hsplit : Real.exp (-(μ * (x + y))) = Real.exp (-(μ * y)) * Real.exp (-(μ * x)) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit, ENNReal.ofReal_mul (Real.exp_pos _).le, ← mul_assoc,
      ENNReal.inv_mul_cancel (by simpa using Real.exp_pos _) ENNReal.ofReal_ne_top, one_mul]
  · have hd : HasDerivAt (fun δ : ℝ => 1 - Real.exp (-(μ * δ))) μ 0 := by
      have h0 := (hasDerivAt_neg_exp_mul_exp (r := μ) (x := 0)).const_add 1
      have e : (fun δ : ℝ => 1 - Real.exp (-(μ * δ))) = fun a => 1 + -Real.exp (-(μ * a)) := by
        funext a; ring
      rw [e]
      exact h0.congr_deriv (by simp)
    have ho := hd.isLittleO
    simp only [mul_zero, neg_zero, Real.exp_zero, sub_self, sub_zero, smul_eq_mul] at ho
    have ho' := ho.mono (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    refine ho'.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [CE904F8A.cdfP P X μ hμ hX hlaw δ (le_of_lt hδ)]
    ring
