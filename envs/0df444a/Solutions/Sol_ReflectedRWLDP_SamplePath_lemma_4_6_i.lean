-- Prove2me | solution 1 for ReflectedRWLDP.SamplePath.lemma_4_6_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T20:48:56.986951+00:00
-- url     : https://prove2.me/submissions/52290a28-0710-4098-b318-5459ffd8e18c

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_MFGLimit_LDP_LDP
import Definitions.Def_ReflectedRWLDP_SamplePath_PathSpace
import Definitions.Def_ReflectedRWLDP_SamplePath_LDP
import Definitions.Def_ReflectedRWLDP_SamplePath_Model
import Definitions.Def_ReflectedRWLDP_SamplePath_RateFunction

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ReflectedRWLDP.SamplePath.L46i

variable {Ω : Type*} [MeasurableSpace Ω]

lemma lindley_nonneg (x₀ : ℝ) (hx₀ : 0 ≤ x₀) (U : ℕ → Ω → ℝ) (ω : Ω) :
    ∀ k, 0 ≤ lindley x₀ U k ω
  | 0 => hx₀
  | k + 1 => le_max_right _ _

/-- Before the first visit to `0`, the reflected walk is the free walk. -/
lemma lindley_eq_sum (x₀ : ℝ) (U : ℕ → Ω → ℝ) (ω : Ω) :
    ∀ k, (∀ j, 1 ≤ j → j ≤ k → lindley x₀ U j ω ≠ 0) →
      lindley x₀ U k ω = x₀ + ∑ i ∈ Finset.range k, U i ω
  | 0, _ => by simp [lindley]
  | k + 1, hk => by
    have ih := lindley_eq_sum x₀ U ω k (fun j hj1 hjk => hk j hj1 (by omega))
    have hne := hk (k + 1) (by omega) le_rfl
    have hstep : lindley x₀ U (k + 1) ω = max (lindley x₀ U k ω + U k ω) 0 := rfl
    rw [hstep] at hne ⊢
    rcases le_total (lindley x₀ U k ω + U k ω) 0 with hle | hle
    · exact absurd (max_eq_right hle) hne
    · rw [max_eq_left hle, ih, Finset.sum_range_succ]; ring

theorem main {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) :
    ∀ t y T : ℝ, 0 ≤ t → 0 ≤ y → 0 < T →
      limsup (fun x : ℝ => speedLog x
          (P {ω | ENNReal.ofReal (x * T) <
            ENat.toENNReal (retTime (fun k => lindley (x * y) U k ω) 1)})) atTop ≤
        ((t * y : ℝ) : EReal) + (T : EReal) * BellWilliams2001.ThresholdPolicy.logMGF P (U 0) t := by
  intro t y T ht hy hT
  have := h.isProbability
  set M := ∫⁻ ω, ENNReal.ofReal (Real.exp (t * U 0 ω)) ∂P with hM
  have hlogM : BellWilliams2001.ThresholdPolicy.logMGF P (U 0) t = ENNReal.log M := rfl
  by_cases hMtop : M = ⊤
  · rw [hlogM, hMtop, ENNReal.log_top, EReal.coe_mul_top_of_pos hT,
      EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
    exact le_top
  -- integrability of `exp (t U_i)`
  have hmeas0 : AEStronglyMeasurable (fun ω => Real.exp (t * U 0 ω)) P :=
    (Real.continuous_exp.measurable.comp ((h.measurable 0).const_mul t)).aestronglyMeasurable
  have hint0 : Integrable (fun ω => Real.exp (t * U 0 ω)) P := by
    refine ⟨hmeas0, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => (Real.exp_pos _).le)]
    exact lt_top_iff_ne_top.mpr hMtop
  have hcomp : Measurable fun u : ℝ => Real.exp (t * u) :=
    Real.continuous_exp.measurable.comp (measurable_const_mul t)
  have hidexp : ∀ i, ProbabilityTheory.IdentDistrib (fun ω => Real.exp (t * U i ω))
      (fun ω => Real.exp (t * U 0 ω)) P P := fun i => (h.identDistrib i).comp hcomp
  have hinti : ∀ i, Integrable (fun ω => Real.exp (t * U i ω)) P := fun i =>
    (hidexp i).integrable_iff.mpr hint0
  set m0 := ProbabilityTheory.mgf (U 0) P t with hm0
  have hm0pos : 0 < m0 := ProbabilityTheory.mgf_pos hint0
  have hMeq : M = ENNReal.ofReal m0 := by
    rw [hM, hm0, ProbabilityTheory.mgf,
      ofReal_integral_eq_lintegral_ofReal hint0 (ae_of_all _ fun ω => (Real.exp_pos _).le)]
  have hmgfi : ∀ i, ProbabilityTheory.mgf (U i) P t = m0 := fun i =>
    (hidexp i).integral_eq
  -- the pointwise bound
  have hbound : ∀ x : ℝ, 0 < x →
      speedLog x (P {ω | ENNReal.ofReal (x * T) <
          ENat.toENNReal (retTime (fun k => lindley (x * y) U k ω) 1)}) ≤
        ((t * y + ((⌊T * x⌋₊ : ℝ) / x) * Real.log m0 : ℝ) : EReal) := by
    intro x hx
    set m := ⌊T * x⌋₊ with hm
    set S : Ω → ℝ := ∑ i ∈ Finset.range m, U i with hS
    have hSapp : ∀ ω, S ω = ∑ i ∈ Finset.range m, U i ω := fun ω => by
      simp [hS, Finset.sum_apply]
    have hsub : {ω | ENNReal.ofReal (x * T) <
          ENat.toENNReal (retTime (fun k => lindley (x * y) U k ω) 1)} ⊆
        {ω | -(x * y) ≤ S ω} := by
      intro ω hω
      simp only [mem_setOf_eq] at hω ⊢
      have hall : ∀ j, 1 ≤ j → j ≤ m → lindley (x * y) U j ω ≠ 0 := by
        intro j hj1 hjm hj0
        have hle : retTime (fun k => lindley (x * y) U k ω) 1 ≤ (j : ℕ∞) := by
          show (⨅ (k : ℕ) (_ : retTime (fun k => lindley (x * y) U k ω) 0 < (k : ℕ∞))
            (_ : lindley (x * y) U k ω = 0), (k : ℕ∞)) ≤ (j : ℕ∞)
          refine iInf_le_of_le j (iInf_le_of_le ?_ (iInf_le_of_le hj0 le_rfl))
          show (0 : ℕ∞) < (j : ℕ∞)
          exact_mod_cast hj1
        have h1 : ENat.toENNReal (retTime (fun k => lindley (x * y) U k ω) 1) ≤
            ENNReal.ofReal (x * T) := by
          refine (ENat.toENNReal_le.mpr hle).trans ?_
          rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
          apply ENNReal.ofReal_le_ofReal
          have : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hjm
          have h2 : (m : ℝ) ≤ T * x := Nat.floor_le (mul_pos hT hx).le
          linarith
        exact absurd hω (not_lt.mpr h1)
      have := lindley_eq_sum (x * y) U ω m hall
      have hnn := lindley_nonneg (x * y) (mul_nonneg hx.le hy) U ω m
      rw [hSapp]
      linarith
    have hindep : ProbabilityTheory.iIndepFun U P := h.indep
    have hintS : Integrable (fun ω => Real.exp (t * S ω)) P := by
      have := hindep.integrable_exp_mul_sum (t := t) h.measurable
        (s := Finset.range m) (fun i _ => hinti i)
      simpa [hS] using this
    have hch := ProbabilityTheory.measure_ge_le_exp_mul_mgf (X := S) (-(x * y)) ht hintS
    have hmgfS : ProbabilityTheory.mgf S P t = m0 ^ m := by
      rw [hS, hindep.mgf_sum h.measurable, Finset.prod_congr rfl (fun i _ => hmgfi i),
        Finset.prod_const, Finset.card_range]
    rw [hmgfS] at hch
    set B := Real.exp (-t * -(x * y)) * m0 ^ m with hB
    have hBpos : 0 < B := mul_pos (Real.exp_pos _) (pow_pos hm0pos _)
    have hPle : P {ω | ENNReal.ofReal (x * T) <
          ENat.toENNReal (retTime (fun k => lindley (x * y) U k ω) 1)} ≤ ENNReal.ofReal B := by
      refine (measure_mono hsub).trans ?_
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal hch
    have hlogB : Real.log B = t * (x * y) + m * Real.log m0 := by
      rw [hB, Real.log_mul (Real.exp_pos _).ne' (pow_pos hm0pos _).ne', Real.log_exp,
        Real.log_pow]
      ring
    unfold speedLog
    calc ((x⁻¹ : ℝ) : EReal) * ENNReal.log (P _)
        ≤ ((x⁻¹ : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal B) :=
          mul_le_mul_of_nonneg_left (ENNReal.log_monotone hPle)
            (by exact_mod_cast (inv_pos.mpr hx).le)
      _ = ((t * y + ((m : ℝ) / x) * Real.log m0 : ℝ) : EReal) := by
          rw [ENNReal.log_ofReal_of_pos hBpos, hlogB, ← EReal.coe_mul]
          congr 1
          field_simp
  -- pass to the limit
  have hlim : Tendsto (fun x : ℝ => ((t * y + ((⌊T * x⌋₊ : ℝ) / x) * Real.log m0 : ℝ) : EReal))
      atTop (𝓝 ((t * y + T * Real.log m0 : ℝ) : EReal)) := by
    apply (continuous_coe_real_ereal.tendsto _).comp
    exact tendsto_const_nhds.add ((tendsto_nat_floor_mul_div_atTop hT.le).mul tendsto_const_nhds)
  calc limsup _ atTop
      ≤ limsup (fun x : ℝ => ((t * y + ((⌊T * x⌋₊ : ℝ) / x) * Real.log m0 : ℝ) : EReal)) atTop :=
        limsup_le_limsup (eventually_gt_atTop 0 |>.mono hbound)
    _ = ((t * y + T * Real.log m0 : ℝ) : EReal) := hlim.limsup_eq
    _ = _ := by
        rw [hlogM, hMeq, ENNReal.log_ofReal_of_pos hm0pos, EReal.coe_add, EReal.coe_mul T]

end ReflectedRWLDP.SamplePath.L46i

open ReflectedRWLDP.SamplePath in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) :
    ∀ t y T : ℝ, 0 ≤ t → 0 ≤ y → 0 < T →
      limsup (fun x : ℝ => speedLog x
          (P {ω | ENNReal.ofReal (x * T) <
            ENat.toENNReal (retTime (fun k => lindley (x * y) U k ω) 1)})) atTop ≤
        ((t * y : ℝ) : EReal) + (T : EReal) * BellWilliams2001.ThresholdPolicy.logMGF P (U 0) t :=
  ReflectedRWLDP.SamplePath.L46i.main P U p h
