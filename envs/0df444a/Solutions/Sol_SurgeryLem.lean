-- Prove2me | solution 1 for SurgeryLem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:36:58.549018+00:00
-- url     : https://prove2.me/submissions/af02cd13-1c6d-4492-92f5-f9c3219cdbd5

import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_Curve
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_Form1
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_surgeryPotential
import Definitions.Def_Tablet_smallPieceCount
import Definitions.Def_Tablet_InitialDeltaExists
import Definitions.Def_Tablet_SurgeryInduction
import Definitions.Def_Tablet_SurgeryLem
import Theorems.Thm_InitialDeltaExists
import Theorems.Thm_SurgeryInduction


set_option autoImplicit false
open Set ENNReal
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (GP : GeodesicPairing E) (γ : Curve E) (ε : ℝ) (n : ℕ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hn : 0 < n)
    (hclosed : IsClosedCurve γ) (hpg : IsPiecewiseGeodesic γ) :
    ∃ (N : ℕ) (g : Fin N → Curve E), 0 < N ∧
      (∀ j, IsClosedCurve (g j)) ∧ (∀ j, IsPiecewiseGeodesic (g j)) ∧
      (∀ ω : Form1 E, curveCurrent γ ω = ∑ j, curveCurrent (g j) ω) ∧
      (∑ j, (g j).len) ≤ (1 + 2 * ε / (1 - ε) + 12 * ε⁻¹ / ((n : ℝ) * (1 - ε))) * γ.len ∧
      (∀ j, morreyNorm (curveMeasure (g j)) ≤ ENNReal.ofReal (4 * ε⁻¹ + 2 * n + 10)) := by
-- BODY
  rcases eq_or_lt_of_le γ.len_nonneg with hlen0 | hlen
  · refine ⟨1, fun _ => γ, one_pos, fun _ => hclosed, fun _ => hpg, ?_, ?_, ?_⟩
    · intro ω
      simp
    · simp only [Fin.sum_univ_one]
      rw [← hlen0]
      simp
    · intro _
      have hicc : Set.Icc (0:ℝ) γ.len = ({0} : Set ℝ) := by
        rw [← hlen0]; simp
      have hzero : (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) γ.len)) = 0 := by
        rw [hicc]
        exact MeasureTheory.Measure.restrict_eq_zero.mpr Real.volume_singleton
      have hmeas : curveMeasure γ = 0 := by
        unfold curveMeasure
        rw [hzero, MeasureTheory.Measure.map_zero]
      rw [hmeas]
      have hmz : morreyNorm (0 : MeasureTheory.Measure E) = 0 := by
        unfold morreyNorm
        simp
      rw [hmz]
      exact zero_le
  · obtain ⟨δ, hdpos, hspc, -⟩ := InitialDeltaExists γ hpg hclosed hlen ε hε0
    obtain ⟨N, g, hN, hcl, hpgj, hcur, hlen', hmor⟩ :=
      SurgeryInduction GP γ δ ε n hε0 hε1 hdpos hn hclosed hpg
    refine ⟨N, g, hN, hcl, hpgj, hcur, ?_, hmor⟩
    rw [hspc] at hlen'
    simpa [surgeryPotential] using hlen'
