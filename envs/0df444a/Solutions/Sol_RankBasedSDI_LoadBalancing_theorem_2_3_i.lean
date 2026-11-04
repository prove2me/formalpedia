-- Prove2me | solution 1 for RankBasedSDI.LoadBalancing.theorem_2_3_i
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T17:56:16.961292+00:00
-- url     : https://prove2.me/submissions/9ed13cee-2a63-4b18-9502-ee0eabcea20c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_Rank
import Definitions.Def_RankBasedSDI_LoadBalancing_PoissonProcess
import Definitions.Def_RankBasedSDI_LoadBalancing_StochasticBasis
import Definitions.Def_RankBasedSDI_LoadBalancing_Reflection
import Definitions.Def_RankBasedSDI_LoadBalancing_CTight
import Definitions.Def_RankBasedSDI_LoadBalancing_RankBasedEquations
import Definitions.Def_RankBasedSDI_LoadBalancing_Model
import Definitions.Def_RankBasedSDI_LoadBalancing_ScaledProcesses
import Theorems.Thm_RankBasedSDI_LoadBalancing_proposition_4_1_iii
import Theorems.Thm_RankBasedSDI_LoadBalancing_eq_5_15
import Theorems.Thm_RankBasedSDI_LoadBalancing_remark_3_2
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open BellWilliams2001.ThresholdPolicy
open RankBasedSDI.LoadBalancing

/-- Projecting a coupling-form convergence onto the first `a` coordinates. -/
theorem couplingConverges_castAdd {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') {a b : ℕ}
    (Z : ℕ → Ω → ℝ → Fin (a + b) → ℝ) (Zlim : Ω' → ℝ → Fin (a + b) → ℝ)
    (h : CouplingConverges P P' Z Zlim) :
    CouplingConverges P P' (fun n ω t k => Z n ω t (Fin.castAdd b k))
      (fun ω t k => Zlim ω t (Fin.castAdd b k)) := by
  obtain ⟨Ω'', m'', P'', Y, Ylim, hP, hY, hYlim, hcad, hconv⟩ := h
  let u : (ℝ≥0 → Fin (a + b) → ℝ) → (ℝ≥0 → Fin a → ℝ) :=
    fun f t k => f t (Fin.castAdd b k)
  have hu : Measurable u := by
    refine measurable_pi_lambda _ (fun t => measurable_pi_lambda _ (fun k => ?_))
    exact (measurable_pi_apply _).comp (measurable_pi_apply t)
  refine ⟨Ω'', m'', P'', fun n ω t k => Y n ω t (Fin.castAdd b k),
    fun ω t k => Ylim ω t (Fin.castAdd b k), hP, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hY] with n hn
    exact hn.comp hu
  · exact hYlim.comp hu
  · intro n ω i
    exact hcad n ω (Fin.castAdd b i)
  · filter_upwards [hconv] with ω hω t ht
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hω t ht)
      (fun _ => zero_le) (fun n => ?_)
    unfold supDist
    refine iSup₂_mono (fun s _ => ENNReal.ofReal_le_ofReal ?_)
    rw [Fin.sum_univ_add (fun i => |Y n ω s i - Ylim ω s i|)]
    have : 0 ≤ ∑ i : Fin b, |Y n ω s (Fin.natAdd a i) - Ylim ω s (Fin.natAdd a i)| :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith

theorem solution {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (S : LoadBalancingSequence Ω N) (H : HeavyTraffic S) (μ₀ : ProbabilityMeasure (Fin N → ℝ))
    (hIC : IC0 S μ₀) :
    ∃ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (F : Filtration ℝ≥0 mΩ')
      (X L B : Ω' → ℝ → Fin N → ℝ),
      IsWeakSolutionSDER (driftB H) (driftM H) (diffSigma H) P' F X L B ∧
      IsWeakSolutionSDIR (driftB H) (driftM H) (diffSigma H) P' F X L B
        (fun ω t => rankDrift (driftB H) (X ω t)) ∧
      HasLaw (fun ω => X ω 0) (μ₀ : Measure (Fin N → ℝ)) P' ∧
      CouplingConverges S.P P'
        (fun n ω t => Fin.append (Xhat S n ω t) (Lhat S n ω t))
        (fun ω t => Fin.append (X ω t) (L ω t)) := by
  obtain ⟨Ω', mΩ', P', F, X, L, B, β, hSDIR, hlaw, hconv⟩ := proposition_4_1_iii S H μ₀ hIC
  have hσ : ∀ i, 0 < diffSigma H i := by
    intro i
    unfold diffSigma
    have h1 := H.lam_pos i
    have h2 := H.mu_pos i
    exact Real.sqrt_pos.mpr (by positivity)
  have hSDER := (eq_5_15 (driftB H) (driftM H) (diffSigma H) hσ P' F X L B β hSDIR).2
  have hSDIR' := (remark_3_2 (driftB H) (driftM H) (diffSigma H) P' F X L B).2 hSDER
  refine ⟨Ω', mΩ', P', F, X, L, B, hSDER, hSDIR', hlaw, ?_⟩
  have := couplingConverges_castAdd S.P P' _ _ hconv
  simpa [Fin.append_left] using this
