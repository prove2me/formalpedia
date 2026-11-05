-- Prove2me | solution 1 for WassFSG.Lip.corollary_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T08:49:13.264286+00:00
-- url     : https://prove2.me/submissions/fd00335f-29e4-4360-893c-701bd47be092
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Lip_Setting
import Definitions.Def_WassFSG_Lip_Rademacher
import Theorems.Thm_WassFSG_Lip_theorem_2
import Theorems.Thm_WassFSG_Lip_lemma_1

open MeasureTheory

theorem solution {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (Ptrue : Measure Z) [IsProbabilityMeasure Ptrue] (τ : ℝ) (hT : WassFSG.Lip.IsT1 τ Ptrue)
    (F : Set (Z → ℝ)) (γ₁ : ℝ) (hF : WassFSG.Lip.LipBound γ₁ F)
    (hF2 : WassFSG.Lip.LipAttainedAtInfinity F)
    (n : ℕ) (hn : 0 < n)
    (ψ : ℝ → ℝ) (h5 : WassFSG.Lip.SubRootLocalComplexity Ptrue n F ψ)
    (rstar : ℝ) (hrstar : 0 < rstar) (hfix : ψ rstar = rstar) (t : ℝ) (ht : 0 < t) :
    (Measure.pi fun _ : Fin n => Ptrue)
        {z | ∃ f ∈ F, ¬ (((∫ x, f x ∂Ptrue : ℝ) : EReal) ≤
          (WassFSG.Lip.empMean z f : EReal)
            + WassFSG.Lip.regularizer (WassFSG.Lip.empMeasure z)
                (2 * Real.sqrt (τ * t / n) + Real.sqrt (4 * rstar + 2 / n)) f
            + ((4 * rstar + 2 / n : ℝ) : EReal))}
      ≤ ENNReal.ofReal ((WassFSG.Lip.peelCount γ₁ τ t n : ℝ) * Real.exp (-t)) := by
  -- the empirical measure of any sample lies in `P₁(Z)`
  have hP1 : ∀ z : Fin n → Z, WassFSG.Lip.IsP1 (WassFSG.Lip.empMeasure z) := by
    intro z
    have hn' : (n : ENNReal) ≠ 0 := by exact_mod_cast hn.ne'
    refine ⟨⟨?_⟩, ?_⟩
    · simp only [WassFSG.Lip.empMeasure, Measure.smul_apply, Measure.coe_finset_sum,
        Finset.sum_apply, measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, smul_eq_mul]
      exact ENNReal.inv_mul_cancel hn' (ENNReal.natCast_ne_top n)
    · simp only [WassFSG.Lip.empMeasure, lintegral_smul_measure, lintegral_finset_sum_measure]
      rw [Finset.sum_congr rfl (fun i _ => lintegral_dirac' (z i) measurable_enorm)]
      refine ENNReal.mul_lt_top (by simpa using hn) ?_
      exact ENNReal.sum_lt_top.2 (fun i _ => enorm_lt_top)
  refine le_trans (measure_mono ?_)
    (WassFSG.Lip.theorem_2 Ptrue τ hT F γ₁ hF n hn ψ h5 rstar hrstar hfix t ht)
  intro z hz
  obtain ⟨f, hfF, hbad⟩ := hz
  refine ⟨f, hfF, fun hgood => hbad ?_⟩
  set ρ := 2 * Real.sqrt (τ * t / n) + Real.sqrt (4 * rstar + 2 / n) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hLf : WassFSG.Lip.LipBound γ₁ ({f} : Set (Z → ℝ)) :=
    ⟨hF.1, fun g hg => by rw [Set.mem_singleton_iff.1 hg]; exact hF.2 f hfF⟩
  have hAf : WassFSG.Lip.LipAttainedAtInfinity ({f} : Set (Z → ℝ)) :=
    ⟨hF2.1, fun g hg => by rw [Set.mem_singleton_iff.1 hg]; exact hF2.2 f hfF⟩
  have hreg := (WassFSG.Lip.lemma_1 (WassFSG.Lip.empMeasure z) (hP1 z) ρ hρ0 f γ₁ hLf).2 hAf
  rw [hreg]
  have : (WassFSG.Lip.empMean z f : EReal) + ((ρ * WassFSG.Conc.lipNorm f : ℝ) : EReal)
      + ((4 * rstar + 2 / n : ℝ) : EReal)
      = ((WassFSG.Lip.empMean z f + ρ * WassFSG.Conc.lipNorm f + 4 * rstar + 2 / n : ℝ) : EReal) := by
    rw [← EReal.coe_add, ← EReal.coe_add]; congr 1; ring
  rw [this]
  exact_mod_cast hgood
