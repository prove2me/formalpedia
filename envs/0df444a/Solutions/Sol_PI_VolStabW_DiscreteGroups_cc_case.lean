-- Prove2me | solution 1 for PI.VolStabW.DiscreteGroups.cc_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:57:50.401053+00:00
-- url     : https://prove2.me/submissions/ea50a62e-7d4d-499a-b350-a4ffd76e8258

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibGlue
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibDis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.DiscreteGroups
open MeasureTheory Topology Set Filter PI.VolStabW PI.VolStabW.Glue
open scoped ENNReal
variable {V : Type} [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
  [SecondCountableTopology V]
variable {X Y : Type} [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}
  (hf : Continuous f) (hι : IsClosedEmbedding ι) (hr : ∀ v, f v ∈ Set.range ι) (hU : IsOpen U)
  (h0 : ∀ b, fib b (f ⁻¹' {ι b} ∩ U)ᶜ = 0) (h2 : ∀ b K, IsCompact K → K ⊆ U → fib b K < ⊤)
  (h3 : ∀ φ : V → ℝ, IsCcOn U φ → (∀ b, Integrable φ (fib b)) ∧
        Continuous (fun b => ∫ v, φ v ∂(fib b)) ∧
        ∀ S : Set X, IsCompact S → ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, ∫ v, φ v ∂(fib b) ∂ν)
include hf hι hr hU h0 h2 h3
namespace PI.VolStabW.DiscreteGroups
theorem _root_.solution (ψ : V → ℝ) (hψ : IsCcOn U ψ) (h0ψ : ∀ v, 0 ≤ ψ v) :
    ∫⁻ v, ENNReal.ofReal (ψ v) ∂μ = ∫⁻ b, ∫⁻ v, ENNReal.ofReal (ψ v) ∂(fib b) ∂ν := by
  obtain ⟨hint, hcont, hS⟩ := h3 ψ hψ
  set S : Set X := ι ⁻¹' (f '' tsupport ψ) with hSdef
  have hSc : IsCompact S := hι.isCompact_preimage (hψ.2.1.image hf)
  have hsub : tsupport ψ ⊆ f ⁻¹' (ι '' S) := by
    intro v hv
    obtain ⟨s, hs⟩ := hr v
    exact ⟨s, ⟨v, hv, hs.symm⟩, hs⟩
  have hzero : ∀ b ∉ S, ∫ v, ψ v ∂(fib b) = 0 := by
    intro b hb
    apply integral_eq_zero_of_ae
    have hae : ∀ᵐ v ∂(fib b), v ∉ (f ⁻¹' {ι b} ∩ U)ᶜ := measure_eq_zero_iff_ae_notMem.1 (h0 b)
    filter_upwards [hae] with v hv
    simp only [mem_compl_iff, not_not] at hv
    exact (eq_or_ne (ψ v) 0).resolve_right fun hne => hb ⟨v, subset_tsupport _ hne, hv.1⟩
  have e1 : ∫ v in f ⁻¹' (ι '' S), ψ v ∂μ = ∫ v, ψ v ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv =>
      image_eq_zero_of_notMem_tsupport fun h => hv (hsub h)
  have e2 : ∫ b in S, (∫ v, ψ v ∂(fib b)) ∂ν = ∫ b, (∫ v, ψ v ∂(fib b)) ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun b hb => hzero b hb
  have hG : Integrable (fun b => ∫ v, ψ v ∂(fib b)) ν :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro' hSc hSc.isClosed hzero)
  have hi : Integrable ψ μ := hψ.1.integrable_of_hasCompactSupport hψ.2.1
  calc ∫⁻ v, ENNReal.ofReal (ψ v) ∂μ = ENNReal.ofReal (∫ v, ψ v ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ h0ψ)).symm
    _ = ENNReal.ofReal (∫ b, (∫ v, ψ v ∂(fib b)) ∂ν) := by rw [← e1, hS S hSc, e2]
    _ = ∫⁻ b, ENNReal.ofReal (∫ v, ψ v ∂(fib b)) ∂ν :=
        ofReal_integral_eq_lintegral_ofReal hG
          (ae_of_all _ fun b => integral_nonneg fun v => h0ψ v)
    _ = ∫⁻ b, ∫⁻ v, ENNReal.ofReal (ψ v) ∂(fib b) ∂ν :=
        lintegral_congr fun b => ofReal_integral_eq_lintegral_ofReal (hint b) (ae_of_all _ h0ψ)
end PI.VolStabW.DiscreteGroups
