-- Prove2me | solution 1 for ShortWDRODual.MaxCost.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:04:28.478088+00:00
-- url     : https://prove2.me/submissions/c6684492-4b29-4f8f-bc67-06dfe54684b5

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_MaxCost_Setting
import Theorems.Thm_ShortWDRODual_MaxCost_ec1_attained
import Theorems.Thm_ShortWDRODual_MaxCost_coupling_form

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.MaxCost
open scoped ENNReal

theorem solution {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (hf : Measurable f) (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (c : X → X → ℝ) (hc : Continuous (fun q : X × X => c q.1 q.2))
    (hcnn : ∀ x y, 0 ≤ c x y) (hc0 : ∀ x, c x x = 0) :
    (∀ ρ : ℝ, 0 ≤ ρ → robustLossMax c f Phat ρ = extIntegral Phat (localSup c f ρ)) ∧
    (∀ lam : ℝ, ShortWDRODual.Legendre.legendre (fun ρ => - robustLossMax c f Phat ρ) (-lam) =
      ⨆ (ρ : ℝ) (_ : 0 ≤ ρ),
        extIntegral Phat (localSup c f ρ) - ((lam * ρ : ℝ) : EReal)) := by
  -- pushing the expectation of `f` along the second marginal
  have hmap : ∀ γ : Measure (X × X),
      extIntegral (γ.map Prod.snd) (fun x => (f x : EReal)) =
        extIntegral γ (fun q => (f q.2 : EReal)) := by
    intro γ
    have h1 : Measurable (fun x => ((f x : EReal)).toENNReal) :=
      measurable_ereal_toENNReal.comp (measurable_coe_real_ereal.comp hf)
    have h2 : Measurable (fun x => (-(f x : EReal)).toENNReal) :=
      measurable_ereal_toENNReal.comp ((measurable_coe_real_ereal.comp hf).neg)
    unfold extIntegral
    rw [lintegral_map h1 measurable_snd, lintegral_map h2 measurable_snd]
  have hofReal : ∀ ρ : ℝ, 0 ≤ ρ → ((ENNReal.ofReal ρ : ℝ≥0∞) : EReal) = (ρ : EReal) := by
    intro ρ hρ
    rw [EReal.coe_ennreal_ofReal, max_eq_left hρ]
  have part1 : ∀ ρ : ℝ, 0 ≤ ρ → robustLossMax c f Phat ρ = extIntegral Phat (localSup c f ρ) := by
    intro ρ hρ
    rw [← coupling_form Phat f hf hfint c hc hcnn hc0 ρ hρ]
    unfold robustLossMax
    apply le_antisymm
    · refine iSup₂_le fun P hP => ?_
      obtain ⟨hPprob, hK⟩ := hP
      have hK' : maxCost c Phat P ≤ ENNReal.ofReal ρ := by
        rw [← EReal.coe_ennreal_le_coe_ennreal_iff, hofReal ρ hρ]
        exact hK
      obtain ⟨γ, hγ, hess⟩ := ec1_attained Phat P c hc hcnn ρ hρ hK'
      obtain ⟨hγp, hγ1, hγ2⟩ := hγ
      refine le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ : Measure (X × X) | γ ∈
          ShortWDRODual.Legendre.couplingsFst Phat ∧
          essSup (fun q : X × X => ENNReal.ofReal (c q.1 q.2)) γ ≤ ENNReal.ofReal ρ}) =>
          extIntegral γ (fun q => (f q.2 : EReal))) γ ⟨⟨hγp, hγ1⟩, hess⟩ ?_
      rw [← hγ2, hmap]
    · refine iSup₂_le fun γ hγ => ?_
      obtain ⟨⟨hγp, hγ1⟩, hess⟩ := hγ
      have : IsProbabilityMeasure (γ.map Prod.snd) :=
        Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
      have hK : maxCost c Phat (γ.map Prod.snd) ≤ ENNReal.ofReal ρ := by
        refine le_trans ?_ hess
        unfold maxCost
        exact iInf₂_le γ ⟨hγp, hγ1, rfl⟩
      have hK' : ((maxCost c Phat (γ.map Prod.snd) : ℝ≥0∞) : EReal) ≤ (ρ : EReal) := by
        rw [← hofReal ρ hρ]
        exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr hK
      refine le_iSup₂_of_le (f := fun (P : Measure X)
          (_ : IsProbabilityMeasure P ∧ ((maxCost c Phat P : ℝ≥0∞) : EReal) ≤ (ρ : EReal)) =>
          extIntegral P (fun x => (f x : EReal))) (γ.map Prod.snd) ⟨this, hK'⟩ ?_
      rw [hmap]
  have hneg : ∀ ρ : ℝ, ρ < 0 → robustLossMax c f Phat ρ = ⊥ := by
    intro ρ hρ
    unfold robustLossMax
    apply le_bot_iff.mp
    refine iSup₂_le fun P hP => ?_
    exfalso
    have h0 : (ρ : EReal) < 0 := by exact_mod_cast hρ
    exact absurd hP.2 (not_le.mpr (lt_of_lt_of_le h0 (EReal.coe_ennreal_nonneg _)))
  have halg : ∀ (E : EReal) (lam ρ : ℝ),
      ((-lam * ρ : ℝ) : EReal) - -E = E - ((lam * ρ : ℝ) : EReal) := by
    intro E lam ρ
    rw [neg_mul, EReal.coe_neg, sub_eq_add_neg, neg_neg, add_comm, ← sub_eq_add_neg]
  refine ⟨part1, ?_⟩
  intro lam
  unfold ShortWDRODual.Legendre.legendre
  apply le_antisymm
  · refine iSup_le fun ρ => ?_
    by_cases hρ : 0 ≤ ρ
    · refine le_iSup₂_of_le (f := fun (ρ : ℝ) (_ : 0 ≤ ρ) =>
          extIntegral Phat (localSup c f ρ) - ((lam * ρ : ℝ) : EReal)) ρ hρ ?_
      simp only
      rw [halg, part1 ρ hρ]
    · simp only
      rw [hneg ρ (lt_of_not_ge hρ), EReal.neg_bot, EReal.sub_top]
      exact bot_le
  · refine iSup₂_le fun ρ hρ => ?_
    refine le_iSup_of_le (f := fun ρ : ℝ =>
      ((-lam * ρ : ℝ) : EReal) - -robustLossMax c f Phat ρ) ρ ?_
    rw [halg, part1 ρ hρ]
