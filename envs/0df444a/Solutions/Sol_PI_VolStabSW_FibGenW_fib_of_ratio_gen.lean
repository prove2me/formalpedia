-- Prove2me | solution 1 for PI.VolStabSW.FibGenW.fib_of_ratio_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:00:13.6188+00:00
-- url     : https://prove2.me/submissions/b732d448-246d-4b47-ba4e-2a3d1fb2b224

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHG
import Theorems.Thm_PI_VolStabSW_fib_of_ratio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.VolStabSW
namespace FibGenW
open MeasureTheory Topology Filter Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
section Core
variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
private theorem isFibreFamily_restrict_of_eqOn_open (μ : Measure V) (ν : Measure X) (f : V → Y) (ι : X → Y)
    (G G' : V → X) (hfG : ∀ x, f x = ι (G x)) (U : Set V) (B : Set X) (fib : X → Measure V)
    (hfib : IsFibreFamily μ f ι U ν B fib) (Q : Set V) (hQo : IsOpen Q)
    (hGG' : ∀ x ∈ Q, G' x = G x) :
    IsFibreFamily μ (fun x => ι (G' x)) ι (U ∩ Q) ν B (fun b => (fib b).restrict Q) := by
  obtain ⟨h1, h2, h3⟩ := hfib
  have hQm : MeasurableSet Q := hQo.measurableSet
  refine ⟨?_, ?_, ?_⟩
  · intro b
    rw [Measure.restrict_apply' hQm]
    refine measure_mono_null ?_ (h1 b)
    intro x ⟨hx1, hxQ⟩ hx2
    apply hx1
    obtain ⟨hx3, hxU⟩ := hx2
    refine ⟨?_, hxU, hxQ⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx3 ⊢
    rw [hGG' x hxQ, ← hfG x]
    exact hx3
  · intro φ hφ
    rw [Set.inter_comm, ← Measure.restrict_restrict hQm, ← lintegral_indicator hQm,
      h2 _ (hφ.indicator hQm)]
    simp only [lintegral_indicator hQm]
  · intro φ hφc hφs hφt
    obtain ⟨hi, hc⟩ := h3 φ hφc hφs (hφt.trans Set.inter_subset_left)
    have hz : ∀ x, x ∉ Q → φ x = 0 := fun x hx => by
      first
        | exact image_eq_zero_of_notMem_tsupport (fun h => hx (hφt h).2)
        | exact image_eq_zero_of_nmem_tsupport (fun h => hx (hφt h).2)
    refine ⟨fun b hb => (hi b hb).restrict, ?_⟩
    have heq : (fun b => ∫ v, φ v ∂(fib b).restrict Q) = fun b => ∫ v, φ v ∂(fib b) :=
      funext fun b => setIntegral_eq_integral_of_forall_compl_eq_zero hz
    rw [heq]
    exact hc
end Core
end FibGenW
open MeasureTheory Topology Filter Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes FibGenW
end PI.VolStabSW
end
end

set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.FibGenW
open MeasureTheory Topology Filter Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
namespace PI.VolStabSW.FibGenW
theorem _root_.solution (μ : Measure V) (ν : Measure X) [ν.IsAddHaarMeasure]
    (f : V → Y) (ι : X → Y) (hι : Function.Injective ι) (G : V → X) (hGc : Continuous G)
    (hfG : ∀ x, f x = ι (G x)) (U : Set V) (B : Set X) (fib : X → Measure V)
    (hfib : IsFibreFamily μ f ι U ν B fib) (T : X) (hB : B ∈ 𝓝 T) (Nb : Set X) (hNb : Nb ∈ 𝓝 T)
    (Q : Set V) (hNbU : ∀ x ∈ Q, G x ∈ Nb → x ∈ U) (hQo : IsOpen Q) (hQcl : IsClosed Q)
    (hQc : IsCompact Q) (H : ℕ → AddSubgroup X) (hHo : ∀ n, IsOpen (H n : Set X))
    (hHc : ∀ n, IsCompact (H n : Set X)) (hHb : ∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N')
    (κ : ℝ) (hratio : ∀ n, μ.real (Q ∩ G ⁻¹' {z | z - T ∈ H n}) = κ * ν.real (H n)) :
    ∫ x, Q.indicator (1 : V → ℂ) x ∂(fib T) = (κ : ℂ) := by
  classical
  have hQm : MeasurableSet Q := hQo.measurableSet
  by_cases hX : ∃ T' : X, T' ≠ T
  · obtain ⟨T', hT'⟩ := hX
    let G' : V → X := Q.piecewise G (fun _ => T')
    have hG'c : Continuous G' := by
      refine hGc.piecewise (fun a ha => ?_) continuous_const
      have hfr : frontier Q = ∅ := IsClopen.frontier_eq ⟨hQcl, hQo⟩
      rw [hfr] at ha
      exact absurd ha (by simp)
    have hGG' : ∀ x ∈ Q, G' x = G x := fun x hx => by simp [G', hx]
    have hNb' : Nb ∩ {T'}ᶜ ∈ 𝓝 T := Filter.inter_mem hNb (isOpen_compl_singleton.mem_nhds hT'.symm)
    have hNbU' : ∀ x, G' x ∈ Nb ∩ {T'}ᶜ → x ∈ U ∩ Q := by
      intro x hx
      by_cases hxQ : x ∈ Q
      · rw [hGG' x hxQ] at hx
        exact ⟨hNbU x hxQ hx.1, hxQ⟩
      · exfalso
        have h' : G' x = T' := by simp [G', hxQ]
        exact hx.2 (by rw [h']; rfl)
    have hratio' : ∀ n, μ.real (Q ∩ G' ⁻¹' {z | z - T ∈ H n}) = κ * ν.real (H n) := by
      intro n
      have hs : Q ∩ G' ⁻¹' {z | z - T ∈ H n} = Q ∩ G ⁻¹' {z | z - T ∈ H n} := by
        ext x
        constructor
        · rintro ⟨hx, h⟩
          exact ⟨hx, by simpa only [Set.mem_preimage, hGG' x hx] using h⟩
        · rintro ⟨hx, h⟩
          exact ⟨hx, by simpa only [Set.mem_preimage, hGG' x hx] using h⟩
      rw [hs]
      exact hratio n
    have key := fib_of_ratio μ ν (fun x => ι (G' x)) ι hι G' hG'c (fun x => rfl) (U ∩ Q) B
      (fun b => (fib b).restrict Q) (isFibreFamily_restrict_of_eqOn_open μ ν f ι G G' hfG U B fib hfib Q hQo hGG') T hB
      (Nb ∩ {T'}ᶜ) hNb' hNbU' Q hQo hQcl hQc H hHo hHc hHb κ hratio'
    have hI : ∫ x in Q, Q.indicator (1 : V → ℂ) x ∂(fib T) = ∫ x, Q.indicator (1 : V → ℂ) x ∂(fib T) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hx])
    rw [← hI]
    exact key
  · push_neg at hX
    have hall : ∀ z : X, z = T := hX
    haveI : Subsingleton X := ⟨fun a b => (hall a).trans (hall b).symm⟩
    have hTN : T ∈ Nb := mem_of_mem_nhds hNb
    have hQU : Q ⊆ U := fun x hx => hNbU x hx (by rw [hall (G x)]; exact hTN)
    obtain ⟨-, h2, -⟩ := hfib
    have hdis := h2 (Q.indicator 1) (measurable_one.indicator hQm)
    simp only [lintegral_indicator_one hQm] at hdis
    rw [Measure.restrict_apply hQm, Set.inter_eq_left.mpr hQU] at hdis
    have hc : (fun b => fib b Q) = fun _ => fib T Q := funext fun b => by rw [hall b]
    rw [hc, lintegral_const] at hdis
    have hr := hratio 0
    have hset : Q ∩ G ⁻¹' {z | z - T ∈ H 0} = Q := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, and_iff_left_iff_imp]
      intro _
      rw [hall (G x), sub_self]
      exact (H 0).zero_mem
    have hH0 : ((H 0 : AddSubgroup X) : Set X) = Set.univ := Set.eq_univ_of_forall fun z => by
      rw [hall z, ← hall 0]
      exact (H 0).zero_mem
    rw [hset, hH0] at hr
    have hν1 : ν Set.univ ≠ 0 := isOpen_univ.measure_ne_zero ν ⟨T, Set.mem_univ _⟩
    have hν2 : ν Set.univ ≠ ⊤ := (isCompact_univ.measure_lt_top).ne
    have hνpos : ν.real Set.univ ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hν1, hν2⟩
    have hint : ∫ x, Q.indicator (1 : V → ℂ) x ∂(fib T) = (((fib T) Q).toReal : ℂ) := by
      rw [show Q.indicator (1 : V → ℂ) = Q.indicator (fun _ => (1 : ℂ)) from rfl,
        integral_indicator_const _ hQm]
      simp [Measure.real]
    rw [hint]
    congr 1
    have h3 := congrArg ENNReal.toReal hdis
    rw [ENNReal.toReal_mul] at h3
    have h' : ((fib T) Q).toReal * ν.real Set.univ = κ * ν.real Set.univ := by
      rw [← hr]
      exact h3.symm
    exact mul_right_cancel₀ hνpos h'
end PI.VolStabSW.FibGenW
