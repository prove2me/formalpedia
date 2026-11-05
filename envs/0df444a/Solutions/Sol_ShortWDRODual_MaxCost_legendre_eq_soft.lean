-- Prove2me | solution 1 for ShortWDRODual.MaxCost.legendre_eq_soft
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:11:53.72262+00:00
-- url     : https://prove2.me/submissions/dcc0295e-7191-4094-ae98-42678b44d6af

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_MaxCost_Setting

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.MaxCost
open scoped ENNReal

theorem solution {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (hf : Measurable f) (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (c : X → X → ℝ) (hc : Continuous (fun q : X × X => c q.1 q.2))
    (hcnn : ∀ x y, 0 ≤ c x y) (hc0 : ∀ x, c x x = 0)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    ShortWDRODual.Legendre.legendre (fun ρ => - robustLossMax c f Phat ρ) (-lam) =
      ⨆ (P : Measure X) (_ : IsProbabilityMeasure P),
        extIntegral P (fun x => (f x : EReal)) - ShortWDRODual.Legendre.lamMul lam (maxCost c Phat P) := by
  have halg : ∀ (E : EReal) (ρ : ℝ),
      ((-lam * ρ : ℝ) : EReal) - -E = E - ((lam * ρ : ℝ) : EReal) := by
    intro E ρ
    rw [neg_mul, EReal.coe_neg, sub_eq_add_neg, neg_neg, add_comm, ← sub_eq_add_neg]
  unfold ShortWDRODual.Legendre.legendre
  set R := ⨆ (P : Measure X) (_ : IsProbabilityMeasure P),
    extIntegral P (fun x => (f x : EReal)) - ShortWDRODual.Legendre.lamMul lam (maxCost c Phat P)
    with hR
  apply le_antisymm
  · refine iSup_le fun ρ => ?_
    rw [halg]
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    unfold robustLossMax
    refine iSup₂_le fun P hP => ?_
    obtain ⟨hPp, hK⟩ := hP
    have hKtop : maxCost c Phat P ≠ ⊤ := by
      intro h
      rw [h, EReal.coe_ennreal_top] at hK
      exact absurd hK (not_le.mpr (EReal.coe_lt_top ρ))
    have hKr : ((maxCost c Phat P).toReal : EReal) = (maxCost c Phat P : EReal) :=
      EReal.coe_ennreal_toReal hKtop
    have hKle : (maxCost c Phat P).toReal ≤ ρ := by
      rw [← hKr] at hK
      exact_mod_cast hK
    have hmul : ShortWDRODual.Legendre.lamMul lam (maxCost c Phat P) =
        ((lam * (maxCost c Phat P).toReal : ℝ) : EReal) := by
      unfold ShortWDRODual.Legendre.lamMul
      rw [if_neg hKtop, ← hKr, ← EReal.coe_mul]
    have h1 : extIntegral P (fun x => (f x : EReal)) -
        ((lam * (maxCost c Phat P).toReal : ℝ) : EReal) ≤ R := by
      rw [← hmul]
      exact le_iSup₂ (f := fun (P : Measure X) (_ : IsProbabilityMeasure P) =>
        extIntegral P (fun x => (f x : EReal)) -
          ShortWDRODual.Legendre.lamMul lam (maxCost c Phat P)) P hPp
    calc extIntegral P (fun x => (f x : EReal))
        = extIntegral P (fun x => (f x : EReal)) -
            ((lam * (maxCost c Phat P).toReal : ℝ) : EReal) +
            ((lam * (maxCost c Phat P).toReal : ℝ) : EReal) := EReal.sub_add_cancel.symm
      _ ≤ R + ((lam * ρ : ℝ) : EReal) := by
          gcongr
  · refine iSup₂_le fun P hPp => ?_
    by_cases hKtop : maxCost c Phat P = ⊤
    · have : ShortWDRODual.Legendre.lamMul lam (maxCost c Phat P) = ⊤ := by
        unfold ShortWDRODual.Legendre.lamMul; rw [if_pos hKtop]
      rw [this, EReal.sub_top]
      exact bot_le
    · set ρ := (maxCost c Phat P).toReal with hρ
      have hKr : (ρ : EReal) = (maxCost c Phat P : EReal) := EReal.coe_ennreal_toReal hKtop
      have hmul : ShortWDRODual.Legendre.lamMul lam (maxCost c Phat P) =
          ((lam * ρ : ℝ) : EReal) := by
        unfold ShortWDRODual.Legendre.lamMul
        rw [if_neg hKtop, ← hKr, ← EReal.coe_mul]
      rw [hmul]
      refine le_iSup_of_le (f := fun ρ : ℝ =>
        ((-lam * ρ : ℝ) : EReal) - -robustLossMax c f Phat ρ) ρ ?_
      rw [halg]
      apply EReal.sub_le_sub _ le_rfl
      unfold robustLossMax
      exact le_iSup₂ (f := fun (P : Measure X)
        (_ : IsProbabilityMeasure P ∧ ((maxCost c Phat P : ℝ≥0∞) : EReal) ≤ (ρ : EReal)) =>
        extIntegral P (fun x => (f x : EReal))) P ⟨hPp, hKr.symm.le⟩
