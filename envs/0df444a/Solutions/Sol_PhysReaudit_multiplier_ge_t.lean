-- Prove2me | solution 1 for PhysReaudit.multiplier_ge_t
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T15:50:29.565185+00:00
-- url     : https://prove2.me/submissions/bbee185d-137a-4cdc-bcc1-1021625ae081

import Mathlib
import Definitions.Def_PhysReaudit_Delta
import Definitions.Def_PhysReaudit_lawQ
import Definitions.Def_PhysReaudit_sprtS

open MeasureTheory ProbabilityTheory PhysReaudit

theorem solution {q₀ t : ℝ} (h0 : 0 < q₀) (h1 : q₀ < t) (h2 : t < 1) {q : ℝ}
    (hq : q ∈ Set.Icc t 1) (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ => bern q)[fun y => Real.exp (sprtS q₀ t y (n + 1) - sprtS q₀ t y n)
        | pastFiltration n]
      =ᵐ[Measure.infinitePi fun _ : ℕ => bern q] (fun _ => 1 + (q - t) * (q₀ - t) / (t * (1 - t))) ∧
    1 + (q - t) * (q₀ - t) / (t * (1 - t)) ≤ 1 := by
  obtain ⟨hqt, hq1⟩ := hq
  have ht0 : 0 < t := h0.trans h1
  have hq0 : 0 ≤ q := by linarith
  haveI hb : IsProbabilityMeasure (bern q) := by
    constructor
    simp only [bern, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hq0 (by linarith)]; simp
  set μ := Measure.infinitePi fun _ : ℕ => bern q with hμ
  set g : Bool → ℝ := fun b => Real.exp (sprtIncr q₀ t b) with hg
  have hf : (fun y : ℕ → Bool => Real.exp (sprtS q₀ t y (n + 1) - sprtS q₀ t y n))
      = fun y => g (y n) := by
    funext y; simp only [hg, sprtS, Finset.sum_range_succ, add_sub_cancel_left]
  refine ⟨?_, ?_⟩
  · rw [hf]
    -- independence of the n-th coordinate from the past
    have hind : iIndepFun (fun i (ω : ℕ → Bool) => ω i) μ :=
      iIndepFun_infinitePi (P := fun _ : ℕ => bern q) (X := fun _ b => b) (fun _ => measurable_id)
    have hI : Indep (⨆ i ∈ ({n} : Set ℕ), MeasurableSpace.comap (fun ω : ℕ → Bool => ω i) inferInstance)
        (⨆ i ∈ ((Finset.range n : Finset ℕ) : Set ℕ),
          MeasurableSpace.comap (fun ω : ℕ → Bool => ω i) inferInstance) μ :=
      indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le) hind
        (by simp)
    simp only [iSup_singleton] at hI
    have hle1 : MeasurableSpace.comap (fun ω : ℕ → Bool => ω n) inferInstance ≤ MeasurableSpace.pi :=
      (measurable_pi_apply n).comap_le
    have hfm : StronglyMeasurable[MeasurableSpace.comap (fun ω : ℕ → Bool => ω n) inferInstance]
        (fun y : ℕ → Bool => g (y n)) :=
      ((measurable_of_countable g).comp (comap_measurable _)).stronglyMeasurable
    have hce := condExp_indep_eq hle1 ((pastFiltration).le n) hfm hI
    refine hce.trans (Filter.Eventually.of_forall (fun _ => ?_))
    -- the mean of the multiplier
    have hmap : ∫ y, g (y n) ∂μ = ∫ b, g b ∂(bern q) := by
      rw [← (measurePreserving_eval_infinitePi (fun _ : ℕ => bern q) n).map_eq,
        integral_map (measurable_pi_apply n).aemeasurable (measurable_of_countable g).aestronglyMeasurable]
    show ∫ y, g (y n) ∂μ = _
    rw [hmap]
    have i1 : Integrable g (Measure.dirac true) := integrable_dirac (by simp)
    have i0 : Integrable g (Measure.dirac false) := integrable_dirac (by simp)
    rw [bern, integral_add_measure (i1.smul_measure ENNReal.ofReal_ne_top)
      (i0.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac, ENNReal.toReal_ofReal hq0, ENNReal.toReal_ofReal (by linarith)]
    simp only [hg, sprtIncr, zMinus, zPlus, if_true, Bool.false_eq_true, if_false, smul_eq_mul]
    rw [Real.exp_log (div_pos h0 ht0), Real.exp_log (div_pos (by linarith) (by linarith))]
    have : (1 - t) ≠ 0 := by linarith
    field_simp; ring
  · have : (q - t) * (q₀ - t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have hd : 0 < t * (1 - t) := mul_pos ht0 (by linarith)
    have := div_nonpos_of_nonpos_of_nonneg this hd.le
    linarith
