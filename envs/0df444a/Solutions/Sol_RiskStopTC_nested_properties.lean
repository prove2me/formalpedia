-- Prove2me | solution 1 for RiskStopTC.nested_properties
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-03T12:17:48.02178+00:00
-- url     : https://prove2.me/submissions/0505e6ee-a628-431e-83ff-efac251312e7

import Definitions.Def_RiskStopTC_IsStoppingFamily
import Definitions.Def_RiskStopTC_nested
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Lean.Elab.Tactic.Omega
open MeasureTheory RiskFunctionals.NestedAVaR RiskStopTC
theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ) (P : Measure[mΩ] Ω)
    [IsProbabilityMeasure P] (p : ENNReal) (hp : 1 ≤ p) (T : ℕ) (hℱ : IsStandardFiltration ℱ T)
    (ϱ : ℕ → (Ω → ℝ) → Ω → ℝ) (hϱ : IsStoppingFamily ℱ P p T ϱ)
    (s t : ℕ) (hst : s ≤ t) (htT : t ≤ T) :
    (∀ X, IsLp (ℱ t) P p X → IsLp (ℱ s) P p (nested ϱ s t X)) ∧
      (∀ X X', IsLp (ℱ t) P p X → IsLp (ℱ t) P p X' → X ≤ᵐ[P] X' →
        nested ϱ s t X ≤ᵐ[P] nested ϱ s t X') ∧
      (∀ X W, IsLp (ℱ t) P p X → IsLp (ℱ s) P p W →
        nested ϱ s t (X + W) =ᵐ[P] nested ϱ s t X + W) ∧
      (∀ X, IsLp (ℱ t) P p X → ∀ A : Set Ω, MeasurableSet[ℱ s] A →
        nested ϱ s t (A.indicator X) =ᵐ[P] A.indicator (nested ϱ s t X)) := by
  classical
  have lp_mono (i j : ℕ) (hij : i ≤ j) (X : Ω → ℝ)
      (hX : IsLp (ℱ i) P p X) : IsLp (ℱ j) P p X :=
    ⟨hX.1.mono (ℱ.mono hij) le_rfl, hX.2⟩
  have lp_add (i : ℕ) (X W : Ω → ℝ) (hX : IsLp (ℱ i) P p X)
      (hW : IsLp (ℱ i) P p W) : IsLp (ℱ i) P p (X + W) :=
    ⟨hX.1.add hW.1, hX.2.add hW.2⟩
  have lp_ind (i : ℕ) (X : Ω → ℝ) (hX : IsLp (ℱ i) P p X)
      (A : Set Ω) (hA : MeasurableSet[ℱ i] A) : IsLp (ℱ i) P p (A.indicator X) :=
    ⟨hX.1.indicator hA, MemLp.indicator ((ℱ.le i) A hA) hX.2⟩
  have cong_step (i : ℕ) (hi : i < T) (X Y : Ω → ℝ)
      (hX : IsLp (ℱ (i + 1)) P p X) (hY : IsLp (ℱ (i + 1)) P p Y)
      (hEq : X =ᵐ[P] Y) : ϱ i X =ᵐ[P] ϱ i Y := by
    filter_upwards [hϱ.monotone i hi X Y hX hY hEq.le,
      hϱ.monotone i hi Y X hY hX hEq.symm.le] with ω hxy hyx
    exact le_antisymm hxy hyx
  induction h : t - s using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases hs : s < t
    · have hs1 : s + 1 ≤ t := by omega
      have hsT : s < T := lt_of_lt_of_le hs htT
      have ih' := ih (t - (s + 1)) (by omega) (s + 1) hs1 rfl
      have heq (X : Ω → ℝ) : nested ϱ s t X = ϱ s (nested ϱ (s + 1) t X) := by
        rw [nested, if_pos hs]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro X hX
        rw [heq]
        exact hϱ.mapsTo s hsT _ (ih'.1 X hX)
      · intro X Y hX hY hXY
        rw [heq, heq]
        exact hϱ.monotone s hsT _ _ (ih'.1 X hX) (ih'.1 Y hY)
          (ih'.2.1 X Y hX hY hXY)
      · intro X W hX hW
        have hW1 := lp_mono s (s + 1) (by omega) W hW
        have hWt := lp_mono s t hst W hW
        have hXW := lp_add t X W hX hWt
        have hinner := ih'.2.2.1 X W hX hW1
        rw [heq, heq]
        exact (cong_step s hsT _ _ (ih'.1 (X + W) hXW)
          (lp_add (s + 1) _ W (ih'.1 X hX) hW1) hinner).trans
          (hϱ.translation s hsT _ W (ih'.1 X hX) hW)
      · intro X hX A hA
        have hA1 : MeasurableSet[ℱ (s + 1)] A := (ℱ.mono (show s ≤ s + 1 by omega)) A hA
        have hAt : MeasurableSet[ℱ t] A := (ℱ.mono hst) A hA
        have hAX := lp_ind t X hX A hAt
        have hinner := ih'.2.2.2 X hX A hA1
        rw [heq, heq]
        exact (cong_step s hsT _ _ (ih'.1 (A.indicator X) hAX)
          (lp_ind (s + 1) _ (ih'.1 X hX) A hA1) hinner).trans
          (hϱ.local s hsT _ (ih'.1 X hX) A hA)
    · have hst' : s = t := Nat.le_antisymm hst (Nat.le_of_not_gt hs)
      subst s
      have hid (X : Ω → ℝ) : nested ϱ t t X = X := by
        rw [nested, if_neg (Nat.lt_irrefl t)]
      simp only [hid]
      exact ⟨fun X hX => hX, fun X Y hX hY hXY => hXY,
        fun X W hX hW => Filter.EventuallyEq.rfl,
        fun X hX A hA => Filter.EventuallyEq.rfl⟩
#print axioms solution
