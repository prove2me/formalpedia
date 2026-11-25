-- Prove2me | solution 1 for PI.VolStabW.DensGen.fib_set
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:14:41.540118+00:00
-- url     : https://prove2.me/submissions/803dd493-68c8-4936-be31-7d5c4e802bcb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensGen
import Theorems.Thm_PI_VolStabW_DensGen_fib_set_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.DensGen
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V} {ν : Measure X} {B : Set X}
  {fib : X → Measure V}
namespace PI.VolStabW.DensGen
theorem _root_.solution [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (ρ : V → ℝ) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (S : Set X) (hS : IsCompact S) (hSB : S ⊆ B) :
    ∫ v in f' ⁻¹' S, ρ v ∂μ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hpc : Continuous fun v => max (ρ v) 0 := hρc.max continuous_const
  have hnc : Continuous fun v => max (-ρ v) 0 := hρc.neg.max continuous_const
  have hps : HasCompactSupport fun v => max (ρ v) 0 :=
    hρs.comp_left (g := fun t : ℝ => max t 0) (by simp)
  have hns : HasCompactSupport fun v => max (-ρ v) 0 :=
    hρs.comp_left (g := fun t : ℝ => max (-t) 0) (by simp)
  have hpU : tsupport (fun v => max (ρ v) 0) ⊆ U := by
    refine (closure_mono fun v hv => ?_).trans hρU
    intro h0
    apply hv
    simp [h0]
  have hnU : tsupport (fun v => max (-ρ v) 0) ⊆ U := by
    refine (closure_mono fun v hv => ?_).trans hρU
    intro h0
    apply hv
    simp [h0]
  have hp3 := hfib.2.2 _ hpc hps hpU
  have hn3 := hfib.2.2 _ hnc hns hnU
  have hsplit : ∀ v, ρ v = max (ρ v) 0 - max (-ρ v) 0 := fun v =>
    (max_zero_sub_eq_self (ρ v)).symm
  have hIp : IntegrableOn (fun b => ∫ v, max (ρ v) 0 ∂(fib b)) S ν :=
    (hp3.2.mono hSB).integrableOn_compact hS
  have hIn : IntegrableOn (fun b => ∫ v, max (-ρ v) 0 ∂(fib b)) S ν :=
    (hn3.2.mono hSB).integrableOn_compact hS
  calc ∫ v in f' ⁻¹' S, ρ v ∂μ
      = ∫ v in f' ⁻¹' S, (max (ρ v) 0 - max (-ρ v) 0) ∂μ := by
        congr 1
        funext v
        exact hsplit v
    _ = ∫ v in f' ⁻¹' S, max (ρ v) 0 ∂μ - ∫ v in f' ⁻¹' S, max (-ρ v) 0 ∂μ :=
        integral_sub (hpc.integrable_of_hasCompactSupport hps).integrableOn
          (hnc.integrable_of_hasCompactSupport hns).integrableOn
    _ = ∫ b in S, (∫ v, max (ρ v) 0 ∂(fib b)) ∂ν -
          ∫ b in S, (∫ v, max (-ρ v) 0 ∂(fib b)) ∂ν := by
        rw [fib_set_nonneg hfib hf' hff' hι _ hpc hps hpU (fun v => le_max_right _ _) S hS hSB,
          fib_set_nonneg hfib hf' hff' hι _ hnc hns hnU (fun v => le_max_right _ _) S hS hSB]
    _ = ∫ b in S, (∫ v, max (ρ v) 0 ∂(fib b) - ∫ v, max (-ρ v) 0 ∂(fib b)) ∂ν :=
        (integral_sub hIp hIn).symm
    _ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by
        refine setIntegral_congr_fun hSm fun b hb => ?_
        rw [← integral_sub (hp3.1 b (hSB hb)) (hn3.1 b (hSB hb))]
        congr 1
        funext v
        exact (hsplit v).symm
end PI.VolStabW.DensGen
