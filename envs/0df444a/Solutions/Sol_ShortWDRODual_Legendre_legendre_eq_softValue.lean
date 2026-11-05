-- Prove2me | solution 1 for ShortWDRODual.Legendre.legendre_eq_softValue
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T11:46:44.747346+00:00
-- url     : https://prove2.me/submissions/937c3e62-bc21-4248-9f2c-5a22b0be7b31

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Legendre_Setting

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.Legendre RWPI.SqrtLasso

theorem solution {X : Type*} [MeasurableSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (c : X → X → ENNReal)
    (hf : Measurable f)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (hc : Measurable (fun p : X × X => c p.1 p.2))
    (hc0 : ∀ x, c x x = 0)
    (lam : ℝ) (hlam : 0 < lam) :
    legendre (fun ρ => - robustLoss c f Phat ρ) (-lam) = softValue c f Phat lam := by
  have halg : ∀ (E : EReal) (ρ : ℝ),
      ((-lam * ρ : ℝ) : EReal) - -E = E - ((lam * ρ : ℝ) : EReal) := by
    intro E ρ
    rw [neg_mul, EReal.coe_neg, sub_eq_add_neg, neg_neg, add_comm, ← sub_eq_add_neg]
  unfold legendre
  apply le_antisymm
  · refine iSup_le fun ρ => ?_
    rw [halg]
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    unfold robustLoss
    refine iSup₂_le fun P hP => ?_
    obtain ⟨hPp, hK⟩ := hP
    have hKtop : transportCost c Phat P ≠ ⊤ := by
      intro h
      rw [h, EReal.coe_ennreal_top] at hK
      exact absurd hK (not_le.mpr (EReal.coe_lt_top ρ))
    have hKr : ((transportCost c Phat P).toReal : EReal) = (transportCost c Phat P : EReal) :=
      EReal.coe_ennreal_toReal hKtop
    have hKle : (transportCost c Phat P).toReal ≤ ρ := by
      rw [← hKr] at hK
      exact_mod_cast hK
    have h1 : extIntegral P (fun x => (f x : EReal)) -
        ((lam * (transportCost c Phat P).toReal : ℝ) : EReal) ≤ softValue c f Phat lam := by
      unfold softValue
      exact le_iSup₂ (f := fun (P : Measure X) (_ : IsProbabilityMeasure P ∧ transportCost c Phat P < ⊤) =>
        extIntegral P (fun x => (f x : EReal)) -
          ((lam * (transportCost c Phat P).toReal : ℝ) : EReal)) P ⟨hPp, lt_top_iff_ne_top.mpr hKtop⟩
    calc extIntegral P (fun x => (f x : EReal))
        = extIntegral P (fun x => (f x : EReal)) -
            ((lam * (transportCost c Phat P).toReal : ℝ) : EReal) +
            ((lam * (transportCost c Phat P).toReal : ℝ) : EReal) := EReal.sub_add_cancel.symm
      _ ≤ softValue c f Phat lam + ((lam * ρ : ℝ) : EReal) := by
          gcongr
  · unfold softValue
    refine iSup₂_le fun P hP => ?_
    obtain ⟨hPp, hKlt⟩ := hP
    have hKtop : transportCost c Phat P ≠ ⊤ := hKlt.ne
    set ρ := (transportCost c Phat P).toReal with hρ
    have hKr : (ρ : EReal) = (transportCost c Phat P : EReal) := EReal.coe_ennreal_toReal hKtop
    refine le_iSup_of_le (f := fun ρ : ℝ =>
      ((-lam * ρ : ℝ) : EReal) - -robustLoss c f Phat ρ) ρ ?_
    rw [halg]
    apply EReal.sub_le_sub _ le_rfl
    unfold robustLoss
    exact le_iSup₂ (f := fun (P : Measure X)
      (_ : IsProbabilityMeasure P ∧ ((transportCost c Phat P : ENNReal) : EReal) ≤ (ρ : EReal)) =>
      extIntegral P (fun x => (f x : EReal))) P ⟨hPp, hKr.symm.le⟩
