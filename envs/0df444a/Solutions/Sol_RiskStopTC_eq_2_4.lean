-- Prove2me | solution 1 for RiskStopTC.eq_2_4
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-04T12:23:55.735581+00:00
-- url     : https://prove2.me/submissions/b658aec7-953d-49e3-a5c4-6095d6717b6b

import Definitions.Def_RiskFunctionals_NestedAVaR_Compositions
import Definitions.Def_MultiperiodRisk_Bellman_TestSet
import Definitions.Def_RiskStopTC_stoppedRV
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Lean.Elab.Tactic.Omega

open MeasureTheory RiskFunctionals.NestedAVaR RiskStopTC
theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ) (P : Measure[mΩ] Ω)
    [IsProbabilityMeasure P] (p : ENNReal) (hp : 1 ≤ p) (T : ℕ) (hℱ : IsStandardFiltration ℱ T)
    (Z : ℕ → Ω → ℝ) (hZ : ∀ t ≤ T, IsLp (ℱ t) P p (Z t))
    (τ : Ω → WithTop ℕ) (hτ : MultiperiodRisk.Bellman.IsBddStoppingTime ℱ T τ) :
    (∀ ω, ∀ t ≤ T, τ ω = (t : WithTop ℕ) → stoppedRV Z τ T ω = Z t ω) ∧
      IsLp (ℱ T) P p (stoppedRV Z τ T) := by
  classical
  constructor
  · intro ω t ht hτt
    unfold stoppedRV
    rw [Finset.sum_eq_single t]
    · simp [hτt]
    · intro s hs hst
      have hneq : τ ω ≠ (s : WithTop ℕ) := by
        rw [hτt]
        intro h
        exact hst (WithTop.coe_injective h.symm)
      simp [hneq]
    · intro htmem
      exact False.elim (htmem (Finset.mem_range.mpr (by omega)))
  · have hterm (t : ℕ) (ht : t ∈ Finset.range (T + 1)) :
        IsLp (ℱ T) P p (({ω | τ ω = (t : WithTop ℕ)}).indicator (Z t)) := by
      have htT : t ≤ T := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using ht
      have hA := hτ.1.measurableSet_eq t
      have hAT : MeasurableSet[ℱ T] {ω | τ ω = (t : WithTop ℕ)} := ℱ.mono htT _ hA
      exact ⟨((hZ t htT).1.mono (ℱ.mono htT) le_rfl).indicator hAT,
        MemLp.indicator (ℱ.le T _ hAT) (hZ t htT).2⟩
    exact ⟨Finset.measurable_sum _ (fun t ht => (hterm t ht).1),
      memLp_finsetSum _ (fun t ht => (hterm t ht).2)⟩
#print axioms solution
