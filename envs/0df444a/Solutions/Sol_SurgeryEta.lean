-- Prove2me | solution 1 for SurgeryEta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:00.046802+00:00
-- url     : https://prove2.me/submissions/fc6f7e46-7384-4b35-a75a-7fdff0bbda0c

import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_Curve
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_Form1
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_SurgeryLem
import Definitions.Def_Tablet_SurgeryEta
import Theorems.Thm_SurgeryLem


set_option autoImplicit false
open Set ENNReal
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (GP : GeodesicPairing E) (γ : Curve E) (η : ℝ)
    (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hclosed : IsClosedCurve γ) (hpg : IsPiecewiseGeodesic γ) :
    ∃ (N : ℕ) (g : Fin N → Curve E), 0 < N ∧
      (∀ j, IsClosedCurve (g j)) ∧ (∀ j, IsPiecewiseGeodesic (g j)) ∧
      (∀ ω : Form1 E, curveCurrent γ ω = ∑ j, curveCurrent (g j) ω) ∧
      (∑ j, (g j).len) ≤ (1 + η) * γ.len ∧
      (∀ j, morreyNorm (curveMeasure (g j)) ≤ ENNReal.ofReal (522 / η ^ 2)) := by
-- BODY
  set ε : ℝ := η / 15 with hε_def
  set n : ℕ := ⌈ε⁻¹ ^ 2⌉₊ with hn_def
  have hε0 : 0 < ε := by rw [hε_def]; linarith
  have hε1 : ε < 1 := by rw [hε_def]; linarith
  have hεne : ε ≠ 0 := ne_of_gt hε0
  have h1mε : (0:ℝ) < 1 - ε := by linarith
  have hn0 : 0 < n := by rw [hn_def]; exact Nat.ceil_pos.mpr (by positivity)
  have hn_ge : ε⁻¹ ^ 2 ≤ (n:ℝ) := by rw [hn_def]; exact Nat.le_ceil _
  have hn_lt : (n:ℝ) < ε⁻¹ ^ 2 + 1 := by rw [hn_def]; exact Nat.ceil_lt_add_one (by positivity)
  have hxpos : (0:ℝ) < (n:ℝ) := lt_of_lt_of_le (by positivity) hn_ge
  obtain ⟨N, g, hN, hcl, hpgj, hcur, hlen', hmor⟩ :=
    SurgeryLem GP γ ε n hε0 hε1 hn0 hclosed hpg
  refine ⟨N, g, hN, hcl, hpgj, hcur, ?_, ?_⟩
  · -- length bound
    have heq : ε⁻¹ ^ 2 * ε = ε⁻¹ := by rw [sq, mul_assoc, inv_mul_cancel₀ hεne, mul_one]
    have hkey : ε⁻¹ ≤ (n:ℝ) * ε := by
      have h := mul_le_mul_of_nonneg_right hn_ge hε0.le
      rwa [heq] at h
    have step2 : 12 * ε⁻¹ / ((n:ℝ) * (1 - ε)) ≤ 12 * ε / (1 - ε) := by
      rw [div_le_div_iff₀ (mul_pos hxpos h1mε) h1mε]
      nlinarith [mul_le_mul_of_nonneg_right hkey h1mε.le]
    have heq2 : 2 * ε / (1 - ε) + 12 * ε / (1 - ε) = 14 * ε / (1 - ε) := by ring
    have step3 : 2 * ε / (1 - ε) + 12 * ε⁻¹ / ((n:ℝ) * (1 - ε)) ≤ 14 * ε / (1 - ε) := by
      linarith [step2, heq2]
    have step4 : 14 * ε / (1 - ε) ≤ η := by
      rw [div_le_iff₀ h1mε, hε_def]
      nlinarith [mul_le_mul_of_nonneg_left hη1 hη0.le]
    have hlenfactor : 1 + 2 * ε / (1 - ε) + 12 * ε⁻¹ / ((n:ℝ) * (1 - ε)) ≤ 1 + η := by
      linarith [step3, step4]
    calc (∑ j, (g j).len)
        ≤ (1 + 2 * ε / (1 - ε) + 12 * ε⁻¹ / ((n:ℝ) * (1 - ε))) * γ.len := hlen'
      _ ≤ (1 + η) * γ.len := mul_le_mul_of_nonneg_right hlenfactor γ.len_nonneg
  · -- Morrey bound
    have hηne : η ≠ 0 := hη0.ne'
    have hεinv : ε⁻¹ = 15 / η := by rw [hε_def, inv_div]
    have hn_lt' : (n:ℝ) ≤ ε⁻¹ ^ 2 + 1 := hn_lt.le
    have hstep_b : 4 * ε⁻¹ + 2 * (ε⁻¹ ^ 2 + 1) + 10 = 60 / η + 450 / η ^ 2 + 12 := by
      rw [hεinv]; ring
    have hkey2 : 60 * η + 450 + 12 * η ^ 2 ≤ 522 := by
      nlinarith [mul_le_mul_of_nonneg_left hη1 hη0.le, hη1, hη0]
    have heq3 : 60 / η + 450 / η ^ 2 + 12 = (60 * η + 450 + 12 * η ^ 2) / η ^ 2 := by
      field_simp
    have hstep_c : 60 / η + 450 / η ^ 2 + 12 ≤ 522 / η ^ 2 := by
      rw [heq3]
      gcongr
    have hmorreyfactor : 4 * ε⁻¹ + 2 * (n:ℝ) + 10 ≤ 522 / η ^ 2 := by
      calc 4 * ε⁻¹ + 2 * (n:ℝ) + 10
          ≤ 4 * ε⁻¹ + 2 * (ε⁻¹ ^ 2 + 1) + 10 := by linarith [hn_lt']
        _ = 60 / η + 450 / η ^ 2 + 12 := hstep_b
        _ ≤ 522 / η ^ 2 := hstep_c
    intro j
    calc morreyNorm (curveMeasure (g j))
        ≤ ENNReal.ofReal (4 * ε⁻¹ + 2 * (n:ℝ) + 10) := hmor j
      _ ≤ ENNReal.ofReal (522 / η ^ 2) := ENNReal.ofReal_le_ofReal hmorreyfactor
