-- Prove2me | solution 1 for RiskStopTC.snell_dominates
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-31T12:18:18.227417+00:00
-- url     : https://prove2.me/submissions/14d6de70-03e7-4aab-9100-813731072c75

import Definitions.Def_RiskStopTC_IsStoppingFamily
import Definitions.Def_RiskStopTC_snell
import Lean.Elab.Tactic.Omega
open MeasureTheory RiskFunctionals.NestedAVaR RiskStopTC
theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ) (P : Measure[mΩ] Ω)
    [IsProbabilityMeasure P] (p : ENNReal) (hp : 1 ≤ p) (T : ℕ) (hℱ : IsStandardFiltration ℱ T)
    (ϱ : ℕ → (Ω → ℝ) → Ω → ℝ) (hϱ : IsStoppingFamily ℱ P p T ϱ)
    (Z : ℕ → Ω → ℝ) (hZ : ∀ t ≤ T, IsLp (ℱ t) P p (Z t)) :
    (∀ t ≤ T, IsLp (ℱ t) P p (snell ϱ Z T t) ∧ Z t ≤ᵐ[P] snell ϱ Z T t) ∧
      ∀ t < T, ϱ t (snell ϱ Z T (t + 1)) ≤ᵐ[P] snell ϱ Z T t := by
  classical
  have hLp : ∀ t ≤ T, IsLp (ℱ t) P p (RiskStopTC.snell ϱ Z T t) := by
    intro t ht
    induction h : T - t using Nat.strong_induction_on generalizing t with
    | h n ih =>
      by_cases hT : T ≤ t
      · have eq : t = T := Nat.le_antisymm ht hT
        subst t
        rw [RiskStopTC.snell, if_pos le_rfl]
        exact hZ T le_rfl
      · have hlt : t < T := Nat.lt_of_not_ge hT
        have hnext := ih (T - (t + 1)) (by omega) (t + 1) (by omega) rfl
        have hstep := hϱ.mapsTo t hlt _ hnext
        have hz := hZ t ht
        rw [RiskStopTC.snell, if_neg hT]
        exact ⟨hz.1.max hstep.1, hz.2.sup hstep.2⟩
  constructor
  · intro t ht
    refine ⟨hLp t ht, ?_⟩
    by_cases hT : T ≤ t
    · have eq : t = T := Nat.le_antisymm ht hT
      subst t
      exact Filter.Eventually.of_forall (fun ω => by
        change Z T ω ≤ RiskStopTC.snell ϱ Z T T ω
        rw [RiskStopTC.snell, if_pos le_rfl])
    · exact Filter.Eventually.of_forall (fun ω => by
        rw [RiskStopTC.snell, if_neg hT]
        exact le_max_left _ _)
  · intro t ht
    exact Filter.Eventually.of_forall (fun ω => by
      conv_rhs => rw [RiskStopTC.snell, if_neg (Nat.not_le_of_lt ht)]
      exact le_max_right _ _)
#print axioms solution
