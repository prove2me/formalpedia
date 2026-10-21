-- Prove2me | solution 1 for TailRiskSharing.TailConv.infConv_monotone
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:06:52.280346+00:00
-- url     : https://prove2.me/submissions/da15f127-0787-4b83-85b1-8aba848e9e3e

import Mathlib
import Definitions.Def_TailRiskSharing_TailConv_Setting

set_option autoImplicit false
open MeasureTheory TailRiskSharing.TailConv

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P) (n : ℕ) (hn : 1 ≤ n)
    (ρ : Fin n → (Ω → ℝ) → ℝ) (j : Fin n) (hmono : TailRiskSharing.VaRTail.IsMonotone P (Linf P) (ρ j)) :
    TailRiskSharing.VaRTail.IsMonotoneE P (Linf P) (TailRiskSharing.VaRConv.infConv (Linf P) ρ) := by
  intro X hX Y hY hXY
  unfold TailRiskSharing.VaRConv.infConv
  refine le_iInf₂ fun Ys hYs => ?_
  obtain ⟨hYsdom, hYssum⟩ := hYs
  set Xs : Fin n → Ω → ℝ := fun i ω => Ys i ω + if i = j then X ω - Y ω else 0 with hXs
  have hXsmem : Xs ∈ TailRiskSharing.VaRConv.Allocations (Linf P) n X := by
    refine ⟨?_, ?_⟩
    · intro i
      by_cases h : i = j
      · subst h
        obtain ⟨hm1, C1, hC1⟩ := hYsdom i
        obtain ⟨hm2, C2, hC2⟩ := hY
        obtain ⟨hm3, C3, hC3⟩ := hX
        refine ⟨?_, C1 + C2 + C3, ?_⟩
        · simp only [hXs, if_true]; fun_prop
        · filter_upwards [hC1, hC2, hC3] with ω h1 h2 h3
          simp only [hXs, if_true]
          calc |Ys i ω + (X ω - Y ω)| ≤ |Ys i ω| + |X ω - Y ω| := abs_add_le _ _
            _ ≤ |Ys i ω| + (|X ω| + |Y ω|) := by gcongr; exact abs_sub _ _
            _ ≤ C1 + C2 + C3 := by linarith
      · simpa [hXs, h] using hYsdom i
    · intro ω
      simp only [hXs, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hYssum ω]; ring
  refine (iInf₂_le Xs hXsmem).trans ?_
  refine EReal.coe_le_coe_iff.mpr ?_
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h : i = j
  · subst h
    refine hmono _ ?_ _ (hYsdom i) ?_
    · exact hXsmem.1 i
    · filter_upwards [hXY] with ω hω
      simp only [hXs, if_true]
      linarith
  · simp [hXs, h]
