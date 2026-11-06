-- Prove2me | solution 1 for ProbabilityTheory.martingale_levyCompensatedSmallJump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:12:51.392288+00:00
-- url     : https://prove2.me/submissions/e8d23345-aa17-4457-9a80-1a80ad76e34f

import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_LeanLevy_RandomMeasure_PoissonMartingale
import Theorems.Thm_ProbabilityTheory_levyCompensatedSmallJumpVersion_ae_eq
import Theorems.Thm_ProbabilityTheory_aestronglyMeasurable_levyCompensatedSmallJump_band
import Theorems.Thm_ProbabilityTheory_levyCompensatedSmallJump_sub
import Theorems.Thm_ProbabilityTheory_indep_prmEvalSigma
import Theorems.Thm_ProbabilityTheory_integral_compensatedPoissonIntegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν]
  {μ : Measure Ω}

/-- The natural-filtration martingale proof, using the original band increment. -/
theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hν : IsLevyMeasure ν) :
    MeasureTheory.Martingale (levyCompensatedSmallJumpVersion hd hν)
      (prmFiltration K X ν hd.measurable_count hd.measurable_point) μ := by
  have hsm : ∀ u : ℝ≥0,
      StronglyMeasurable[prmEvalSigma K X (volume.prod ν)
        (Set.Iic (u : ℝ) ×ˢ Set.univ)]
        (levyCompensatedSmallJumpVersion hd hν u) := by
    intro u
    unfold levyCompensatedSmallJumpVersion
    exact AEStronglyMeasurable.stronglyMeasurable_mk _
  have hint : ∀ u : ℝ≥0,
      Integrable (levyCompensatedSmallJumpVersion hd hν u) μ := by
    intro u
    exact ((Lp.memLp (levyCompensatedSmallJump hd hν (u : ℝ))).integrable
      one_le_two).congr
        (levyCompensatedSmallJumpVersion_ae_eq hd hν u).symm
  refine ⟨fun u => hsm u, fun s t hst => ?_⟩
  change μ[levyCompensatedSmallJumpVersion hd hν t |
    prmEvalSigma K X (volume.prod ν)
      (Set.Iic (s : ℝ) ×ˢ Set.univ)] =ᵐ[μ]
    levyCompensatedSmallJumpVersion hd hν s
  have hband := aestronglyMeasurable_levyCompensatedSmallJump_band
    hd hν (s : ℝ) (t : ℝ)
  set cb : Ω → ℝ := hband.mk _ with hcbdef
  have hcb_sm : StronglyMeasurable[prmEvalSigma K X (volume.prod ν)
      (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ Set.univ)] cb :=
    hband.stronglyMeasurable_mk
  have hcb_ae : cb =ᵐ[μ]
      ⇑(compensatedPoissonIntegral hd
        ((memLp_two_smallJumpBandFun hν (s : ℝ) (t : ℝ)).toLp _)) :=
    hband.ae_eq_mk.symm
  have hincr : levyCompensatedSmallJumpVersion hd hν t
      =ᵐ[μ] levyCompensatedSmallJumpVersion hd hν s + cb := by
    have hlpsub : ⇑(levyCompensatedSmallJump hd hν (t : ℝ))
        - ⇑(levyCompensatedSmallJump hd hν (s : ℝ)) =ᵐ[μ] cb := by
      refine (Lp.coeFn_sub _ _).symm.trans ?_
      rw [levyCompensatedSmallJump_sub hd hν
        (NNReal.coe_nonneg s) (by exact_mod_cast hst)]
      exact hcb_ae.symm
    filter_upwards [levyCompensatedSmallJumpVersion_ae_eq hd hν t,
      levyCompensatedSmallJumpVersion_ae_eq hd hν s, hlpsub]
      with ω hVt hVs hlp
    simp only [Pi.add_apply, Pi.sub_apply] at *
    rw [hVt, hVs, ← hlp]
    ring
  have hle_s := prmEvalSigma_le (m := volume.prod ν)
    hd.measurable_count hd.measurable_point
    (Set.Iic (s : ℝ) ×ˢ Set.univ)
  have hle_band := prmEvalSigma_le (m := volume.prod ν)
    hd.measurable_count hd.measurable_point
    (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ Set.univ)
  haveI : IsFiniteMeasure (μ.trim hle_s) := isFiniteMeasure_trim hle_s
  have hindep : Indep
      (prmEvalSigma K X (volume.prod ν)
        (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ Set.univ))
      (prmEvalSigma K X (volume.prod ν)
        (Set.Iic (s : ℝ) ×ˢ Set.univ)) μ :=
    indep_prmEvalSigma hd
      (Set.Disjoint.set_prod_left
        (Set.Iic_disjoint_Ioc (le_refl (s : ℝ))).symm Set.univ Set.univ)
  have hmean : (∫ ω, cb ω ∂μ) = 0 := by
    rw [integral_congr_ae hcb_ae]
    exact integral_compensatedPoissonIntegral hd _
  have hcb0 : μ[cb | prmEvalSigma K X (volume.prod ν)
      (Set.Iic (s : ℝ) ×ˢ Set.univ)] =ᵐ[μ] 0 := by
    have hkey := condExp_indep_eq hle_band hle_s hcb_sm hindep
    simp only [hmean] at hkey
    exact hkey
  refine (condExp_congr_ae hincr).trans ?_
  refine (condExp_add (hint s)
    (((Lp.memLp _).integrable one_le_two).congr hcb_ae.symm) _).trans ?_
  rw [condExp_of_stronglyMeasurable hle_s (hsm s) (hint s)]
  calc levyCompensatedSmallJumpVersion hd hν s
        + μ[cb | prmEvalSigma K X (volume.prod ν)
          (Set.Iic (s : ℝ) ×ˢ Set.univ)]
      =ᵐ[μ] levyCompensatedSmallJumpVersion hd hν s + (0 : Ω → ℝ) :=
        by
          filter_upwards [hcb0] with ω hω
          simp only [Pi.add_apply]
          rw [hω]
    _ = levyCompensatedSmallJumpVersion hd hν s := add_zero _
