-- Prove2me | solution 1 for RapidRatePoisson.WeakConv.theorem_1_of_indepF
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T11:16:00.105783+00:00
-- url     : https://prove2.me/submissions/e95e89ea-7d93-49fe-9c6b-f1c70836af72
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_RapidRatePoisson_WeakConv_poisson_limit_dvj
import Theorems.Thm_RapidRatePoisson_WeakConv_thinned_compensator
import Theorems.Thm_RapidRatePoisson_WeakConv_thinned_simple
import Theorems.Thm_RapidRatePoisson_WeakConv_scaledComp_tendsto_of_A0

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open RapidRatePoisson.WeakConv

theorem solution {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 m) (N A : ℝ≥0 → Ω → ℝ) (lamStar : ℝ≥0)
    (hN : ∀ ω, MartingaleHT.InfiniteServer.IsUnitJumpCountingPath (fun t => N t ω))
    (hA : IsCompensator F P N A) (hA1 : Assumption1 P A lamStar)
    (hNint : ∀ t, Integrable (N t) P)
    (β : ℝ≥0 → ℕ → Ω → Bool)
    (hβ : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 → IsBernoulliSeq P ε (β ε) ∧
      Indep (MeasurableSpace.comap (markSeq (β ε)) inferInstance) (⨆ t, F t) P)
    (εs : ℕ → ℝ≥0) (hεs : ∀ n, 0 < εs n ∧ εs n ≤ 1) (hεs0 : Tendsto εs atTop (𝓝 0))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (N0 : Ω' → ℝ → ℝ) (hN0 : RankBasedSDI.LoadBalancing.IsPoissonProcess P' lamStar N0) :
    PuhaWardFluid.Limit.ConvInDist (fun a b : ℝ => dist a b) P
      (fun n ω t => thinned N (β (εs n)) (εs n) t ω) P' (fun ω (t : ℝ≥0) => N0 ω t) := by
  -- §2, p. 3: for each `n`, `A_{ε_n}` is the `G^{ε_n}`-compensator of `N_{ε_n}`
  have hcomp : ∀ n, ∃ G : Filtration ℝ≥0 m, (∀ t, G t = gSigma F N (β (εs n)) (εs n) t) ∧
      IsCompensator G P (thinned N (β (εs n)) (εs n)) (scaledComp A (εs n)) := fun n =>
    thinned_compensator P F N A hN hA hNint (εs n) (hεs n).1 (hεs n).2 (β (εs n))
      (hβ (εs n) (hεs n).1 (hεs n).2).1 (hβ (εs n) (hεs n).1 (hεs n).2).2
  choose G _ hG using hcomp
  -- proof of Theorem 1: `A_{ε_n}(t) → λ* t` in probability
  have hεs' : Tendsto εs atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hεs0, Eventually.of_forall fun n => (hεs n).1⟩
  have hconv : ∀ t : ℝ≥0, TendstoInMeasure P (fun n => scaledComp A (εs n) t) atTop
      (fun _ => (lamStar : ℝ) * t) := by
    intro t δ hδ
    exact (scaledComp_tendsto_of_A0 P A lamStar hA.1 hA1 t δ hδ).comp hεs'
  -- Theorem 13.4.IV of Daley and Vere-Jones
  exact poisson_limit_dvj P G (fun n => thinned N (β (εs n)) (εs n))
    (fun n => scaledComp A (εs n)) lamStar
    (fun n ω => (thinned_simple N (β (εs n)) (εs n) (hεs n).1 (hεs n).2).1 ω (hN ω))
    hG hconv P' N0 hN0
