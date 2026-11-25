-- Prove2me | solution 1 for PI.VolStabSW.DensGen.fib_set
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:59:23.446816+00:00
-- url     : https://prove2.me/submissions/cbed974d-1243-41b1-a9db-6d4199f53599

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensGen
import Theorems.Thm_PI_VolStabSW_DensGen_fib_set_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.DensGen
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V} {ν : Measure X} {B : Set X}
  {fib : X → Measure V}
namespace PI.VolStabSW.DensGen
theorem _root_.solution [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (ρ : V → ℝ) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (S : Set X) (hS : IsCompact S) (hSB : S ⊆ B) :
    ∫ v in f' ⁻¹' S, ρ v ∂μ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by
  set ρp : V → ℝ := fun v => max (ρ v) 0 with hρpdef
  set ρn : V → ℝ := fun v => max (-ρ v) 0 with hρndef
  have hρeq : ρ = fun v => ρp v - ρn v :=
    funext fun v => (max_zero_sub_max_neg_zero_eq_self (ρ v)).symm
  have hcp : Continuous ρp := hρc.max continuous_const
  have hcn : Continuous ρn := hρc.neg.max continuous_const
  have hsp : HasCompactSupport ρp := hρs.comp_left (g := fun x : ℝ => max x 0) (by simp)
  have hsn : HasCompactSupport ρn := hρs.neg.comp_left (g := fun x : ℝ => max x 0) (by simp)
  have hup : tsupport ρp ⊆ U := (tsupport_comp_subset (g := fun x : ℝ => max x 0) (by simp) ρ).trans hρU
  have hun : tsupport ρn ⊆ U := by
    refine (tsupport_comp_subset (g := fun x : ℝ => max x 0) (by simp) (-ρ)).trans ?_
    rw [tsupport_neg]
    exact hρU
  have hp := fib_set_nonneg hfib hf' hff' hι ρp hcp hsp hup (fun v => le_max_right _ _) S hS hSB
  have hn := fib_set_nonneg hfib hf' hff' hι ρn hcn hsn hun (fun v => le_max_right _ _) S hS hSB
  have hip : Integrable ρp μ := hcp.integrable_of_hasCompactSupport hsp
  have hin : Integrable ρn μ := hcn.integrable_of_hasCompactSupport hsn
  obtain ⟨hintp, hGp⟩ := hfib.2.2 ρp hcp hsp hup
  obtain ⟨hintn, hGn⟩ := hfib.2.2 ρn hcn hsn hun
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  calc ∫ v in f' ⁻¹' S, ρ v ∂μ = ∫ v in f' ⁻¹' S, ρp v ∂μ - ∫ v in f' ⁻¹' S, ρn v ∂μ := by
        rw [hρeq]
        exact integral_sub hip.integrableOn hin.integrableOn
    _ = ∫ b in S, (∫ v, ρp v ∂(fib b)) ∂ν - ∫ b in S, (∫ v, ρn v ∂(fib b)) ∂ν := by rw [hp, hn]
    _ = ∫ b in S, ((∫ v, ρp v ∂(fib b)) - ∫ v, ρn v ∂(fib b)) ∂ν :=
        (integral_sub ((hGp.mono hSB).integrableOn_compact hS)
          ((hGn.mono hSB).integrableOn_compact hS)).symm
    _ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by
        refine setIntegral_congr_fun hSm (fun b hb => ?_)
        rw [hρeq]
        exact (integral_sub (hintp b (hSB hb)) (hintn b (hSB hb))).symm
end PI.VolStabSW.DensGen
