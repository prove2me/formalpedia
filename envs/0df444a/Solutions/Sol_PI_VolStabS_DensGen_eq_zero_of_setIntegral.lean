-- Prove2me | solution 1 for PI.VolStabS.DensGen.eq_zero_of_setIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:06:59.107109+00:00
-- url     : https://prove2.me/submissions/471c514e-ef45-47fd-b48b-07b2f12c7c0a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_DensGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS PI.VolStabS.DensGen
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V} {ν : Measure X} {B : Set X}
  {fib : X → Measure V}
namespace PI.VolStabS.DensGen
theorem _root_.solution [LocallyCompactSpace X] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] (D : X → ℝ) (W : Set X) (b0 : X) (hW : W ∈ 𝓝 b0)
    (hD : ContinuousOn D W) (h0 : ∀ S, IsCompact S → S ⊆ W → ∫ b in S, D b ∂ν = 0) :
    D b0 = 0 := by
  have key : ∀ E : X → ℝ, ContinuousOn E W →
      (∀ S, IsCompact S → S ⊆ W → ∫ b in S, E b ∂ν = 0) → ¬ 0 < E b0 := by
    intro E hE h0E hpos
    have hca : ContinuousAt E b0 := hE.continuousAt hW
    have hnhd : E ⁻¹' Set.Ioi (E b0 / 2) ∈ 𝓝 b0 := hca.preimage_mem_nhds (Ioi_mem_nhds (by linarith))
    obtain ⟨K, hK, hKsub, hKc⟩ := local_compact_nhds (Filter.inter_mem hnhd hW)
    have hKW : K ⊆ W := fun x hx => (hKsub hx).2
    have hpos' : 0 < ν K := Measure.measure_pos_of_mem_nhds ν hK
    have hfin : ν K < ⊤ := hKc.measure_lt_top
    have hint : IntegrableOn E K ν := (hE.mono hKW).integrableOn_compact hKc
    have hconst : IntegrableOn (fun _ => E b0 / 2) K ν := by
      first
        | exact integrableOn_const hfin.ne
        | exact integrableOn_const.2 (Or.inr hfin)
        | exact (integrableOn_const (C := E b0 / 2)).2 (Or.inr hfin)
    have hmono : ∫ b in K, E b0 / 2 ∂ν ≤ ∫ b in K, E b ∂ν :=
      setIntegral_mono_on hconst hint hKc.measurableSet (fun x hx => (hKsub hx).1.le)
    rw [h0E K hKc hKW, setIntegral_const] at hmono
    have hr : 0 < (ν K).toReal := ENNReal.toReal_pos hpos'.ne' hfin.ne
    first
      | (rw [smul_eq_mul] at hmono; nlinarith)
      | (simp only [Measure.real, smul_eq_mul] at hmono; nlinarith)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine key (fun b => -D b) hD.neg (fun S hS hSW => ?_) (by simpa using hneg)
    rw [integral_neg, h0 S hS hSW, neg_zero]
  · exact key D hD h0 hpos
end PI.VolStabS.DensGen
