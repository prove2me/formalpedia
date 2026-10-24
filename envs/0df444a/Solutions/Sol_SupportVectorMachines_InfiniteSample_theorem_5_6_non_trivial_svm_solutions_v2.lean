-- Prove2me | solution 1 for SupportVectorMachines.InfiniteSample.theorem_5_6_non_trivial_svm_solutions_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T14:59:27.088994+00:00
-- url     : https://prove2.me/submissions/73b7b7e6-e491-4e40-bcf9-7d183cee79df

import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss_v2
import Definitions.Def_SupportVectorMachines_InfiniteSample_NemitskiLoss_v2
import Definitions.Def_SupportVectorMachines_InfiniteSample_IsRKHSOfKernel
import Definitions.Def_SupportVectorMachines_InfiniteSample_populationRisk_v2

open MeasureTheory

open SupportVectorMachines.InfiniteSample in
theorem solution {X : Type*} [MeasurableSpace X]
    (L : Loss X) (hL : ∀ x y, ConvexOn ℝ Set.univ (L x y))
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P] (hNem : PIntegrableNemitskiLoss L P)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hk : ∀ x, Measurable (fun x' => k x' x))
    (hkBdd : ∃ M : ℝ, ∀ x : X, k x x ≤ M)
    (hgap : (⨅ f : H, populationRisk L P (toFun f)) < populationRisk L P (fun _ => 0))
    (lam : ℝ) (hlam : 0 < lam) (fPlam : H)
    (hmin : ∀ g : H, ENNReal.ofReal (lam * ‖fPlam‖ ^ 2) + populationRisk L P (toFun fPlam) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g)) :
    fPlam ≠ 0 := by
  intro h0
  subst h0
  have hz : toFun 0 = fun _ => 0 := by rw [map_zero]; rfl
  rw [hz] at hmin
  set R0 := populationRisk L P (fun _ => 0) with hR0
  -- finiteness of R0
  obtain ⟨b, h, hb0, hh0, -, hLb, hbint⟩ := hNem
  have hR0fin : R0 < ⊤ := by
    have hi : Integrable (fun p : X × ℝ => b p.1 p.2 + h 0) P := hbint.add (integrable_const _)
    calc R0 ≤ ∫⁻ p, ENNReal.ofReal (b p.1 p.2 + h 0) ∂P := by
          apply lintegral_mono; intro p
          apply ENNReal.ofReal_le_ofReal
          simpa using hLb p.1 p.2 0
      _ ≤ ∫⁻ p, ‖b p.1 p.2 + h 0‖ₑ ∂P := lintegral_ofReal_le_lintegral_enorm _
      _ < ⊤ := hi.hasFiniteIntegral
  obtain ⟨g, hg⟩ := iInf_lt_iff.1 hgap
  have hgfin : populationRisk L P (toFun g) < ⊤ := hg.trans hR0fin
  set a := R0.toReal
  set c := (populationRisk L P (toFun g)).toReal
  have hca : c < a := (ENNReal.toReal_lt_toReal hgfin.ne hR0fin.ne).2 hg
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  -- convexity bound
  have hconv : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      populationRisk L P (toFun (t • g)) ≤ ENNReal.ofReal ((1 - t) * a + t * c) := by
    intro t ht0 ht1
    have hpt : ∀ p : X × ℝ, ENNReal.ofReal (L p.1 p.2 (toFun (t • g) p.1)) ≤
        ENNReal.ofReal (1 - t) * ENNReal.ofReal (L p.1 p.2 0) +
          ENNReal.ofReal t * ENNReal.ofReal (L p.1 p.2 (toFun g p.1)) := by
      intro p
      rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul ht0,
        ← ENNReal.ofReal_add (mul_nonneg (by linarith) (L.nonneg _ _ _))
          (mul_nonneg ht0 (L.nonneg _ _ _))]
      apply ENNReal.ofReal_le_ofReal
      have := (hL p.1 p.2).2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (toFun g p.1))
        (show 0 ≤ 1 - t by linarith) ht0 (by ring)
      simp only [smul_eq_mul, mul_zero, zero_add] at this
      simpa [map_smul, Pi.smul_apply, smul_eq_mul] using this
    have hmeas : Measurable (fun p : X × ℝ =>
        ENNReal.ofReal (1 - t) * ENNReal.ofReal (L p.1 p.2 0)) := by
      have : Measurable (fun p : X × ℝ => L p.1 p.2 0) :=
        L.measurable.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
      exact (ENNReal.measurable_ofReal.comp this).const_mul _
    calc populationRisk L P (toFun (t • g))
        ≤ ∫⁻ p, (ENNReal.ofReal (1 - t) * ENNReal.ofReal (L p.1 p.2 0) +
          ENNReal.ofReal t * ENNReal.ofReal (L p.1 p.2 (toFun g p.1))) ∂P :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (1 - t) * R0 + ENNReal.ofReal t * populationRisk L P (toFun g) := by
          rw [lintegral_add_left hmeas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          rfl
      _ = ENNReal.ofReal ((1 - t) * a + t * c) := by
          rw [← ENNReal.ofReal_toReal hR0fin.ne, ← ENNReal.ofReal_toReal hgfin.ne,
            ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul ht0,
            ← ENNReal.ofReal_add (mul_nonneg (by linarith) ENNReal.toReal_nonneg)
              (mul_nonneg ht0 ENNReal.toReal_nonneg)]
  set G := ‖g‖ ^ 2
  have hG : 0 ≤ G := by positivity
  set t := min 1 ((a - c) / (2 * (lam * G + 1)))
  have hden : 0 < 2 * (lam * G + 1) := by positivity
  have ht0 : 0 < t := lt_min one_pos (div_pos (by linarith) hden)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ (a - c) / (2 * (lam * G + 1)) := min_le_right _ _
  have key := (hmin (t • g)).trans (add_le_add_right (hconv t ht0.le ht1) _)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at key
  have ha0 : 0 ≤ a := hc0.trans hca.le
  rw [show (‖(0:H)‖) = 0 from norm_zero, ← ENNReal.ofReal_toReal hR0fin.ne,
    ← ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_add (by positivity) (by nlinarith)] at key
  have key2 := (ENNReal.ofReal_le_ofReal_iff (by nlinarith)).1 key
  -- key2 : lam*0^2 + a ≤ lam*(t*‖g‖)^2 + ((1-t)*a + t*c)
  have h3 : t * (a - c) ≤ lam * t ^ 2 * G := by nlinarith
  have h4 : a - c ≤ lam * t * G := by
    have := (mul_le_mul_iff_of_pos_left ht0).1 (by nlinarith : t * (a - c) ≤ t * (lam * t * G))
    exact this
  have h5 : lam * t * G ≤ (a - c) / 2 := by
    have : t * (2 * (lam * G + 1)) ≤ a - c := (le_div_iff₀ hden).1 ht2
    nlinarith
  linarith
