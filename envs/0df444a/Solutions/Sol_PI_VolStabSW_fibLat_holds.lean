-- Prove2me | solution 1 for PI.VolStabSW.fibLat_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:18:27.181548+00:00
-- url     : https://prove2.me/submissions/8bafdb2a-f073-4123-9a73-57e4a6990a24

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_HenselCountHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHF
import Theorems.Thm_PI_VolStabSW_fib_of_ratio
import Theorems.Thm_PI_VolStabSW_cos_ratio
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
open MeasureTheory Topology Filter Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
section Core
variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
end Core
section Lat
variable {V X : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
end Lat
section Fin
variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
end Fin
private lemma eq_of_mul_mul_eq_of_det_ne_zero {a b c : ENNReal} (h0 : c ≠ 0) (ht : c ≠ ⊤) (h : a * c = b * c) :
    a = b := by
  have h1 : a = b * c / c := (ENNReal.eq_div_iff h0 ht).2 (by rw [mul_comm]; exact h)
  have h2 : b = b * c / c := (ENNReal.eq_div_iff h0 ht).2 (mul_comm c b)
  rw [h1, ← h2]
end PI.VolStabSW
end
end

set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Topology Filter Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace PI.VolStabSW
theorem _root_.solution : FibLat := by
  unfold FibLat
  intro V X Y i1 i2 i3 i4 i5 i6 i7 i8 j1 j2 j3 j4 j5 j6 j7 j8 μ ν hμ hν f ι hι G hGc hfG U B fib hfib
    T hB Nb hNb hNbU L hLo hLc Λ H hΛL hΛo hΛc hΛa hHo hHc hHb hhens
  haveI := hμ
  haveI := hν
  classical
  have hLcl : IsClosed (L : Set V) := AddSubgroup.isClosed_of_isOpen L hLo
  by_cases hgood : ∃ y ∈ L, G y - T ∈ H 0
  · obtain ⟨y₀, hy₀L, hy₀⟩ := hgood
    obtain ⟨D₀, hD₀, -⟩ := hhens y₀ hy₀L hy₀
    have hHsub : ∀ n, H n ≤ H 0 := by
      intro n
      rw [← hD₀ n, ← hD₀ 0]
      exact AddSubgroup.map_mono (hΛa (Nat.zero_le n))
    have hcos_open : ∀ x, IsOpen {z | z - x ∈ Λ 0} := fun x =>
      (hΛo 0).preimage (continuous_id.sub continuous_const)
    have hAo : ∀ n, IsOpen (G ⁻¹' {z | z - T ∈ H n}) := fun n =>
      ((hHo n).preimage (continuous_id.sub continuous_const)).preimage hGc
    have hsame : ∀ x x', x' - x ∈ Λ 0 → {z | z - x ∈ Λ 0} = {z | z - x' ∈ Λ 0} := by
      intro x x' hxx'
      ext z
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        simpa using (Λ 0).sub_mem h hxx'
      · intro h
        simpa using (Λ 0).add_mem h hxx'
    obtain ⟨C, hCdef⟩ : ∃ C : Set (Set V), C = {c | ∃ x ∈ L, c = {z | z - x ∈ Λ 0}} := ⟨_, rfl⟩
    have hmemC : ∀ c, c ∈ C ↔ ∃ x ∈ L, c = {z | z - x ∈ Λ 0} := by
      intro c
      rw [hCdef]
      rfl
    have hdisj : C.PairwiseDisjoint id := by
      intro c₁ h₁ c₂ h₂ hne
      obtain ⟨x₁, -, rfl⟩ := (hmemC c₁).1 h₁
      obtain ⟨x₂, -, rfl⟩ := (hmemC c₂).1 h₂
      change Disjoint {z | z - x₁ ∈ Λ 0} {z | z - x₂ ∈ Λ 0}
      rw [Set.disjoint_left]
      intro z hz1 hz2
      apply hne
      exact hsame x₁ x₂ (by simpa using (Λ 0).sub_mem hz1 hz2)
    have hcount : C.Countable :=
      hdisj.countable_of_isOpen
        (fun c hc => by
          obtain ⟨x, -, rfl⟩ := (hmemC c).1 hc
          exact hcos_open x)
        (fun c hc => by
          obtain ⟨x, -, rfl⟩ := (hmemC c).1 hc
          exact ⟨x, by show x - x ∈ Λ 0; rw [sub_self]; exact (Λ 0).zero_mem⟩)
    have hunion : ∀ n, (L : Set V) ∩ G ⁻¹' {z | z - T ∈ H n} =
        ⋃ c ∈ C, c ∩ G ⁻¹' {z | z - T ∈ H n} := by
      intro n
      ext z
      simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨hzL, hzA⟩
        exact ⟨{w | w - z ∈ Λ 0}, (hmemC _).2 ⟨z, hzL, rfl⟩,
          by show z - z ∈ Λ 0; rw [sub_self]; exact (Λ 0).zero_mem, hzA⟩
      · rintro ⟨c, hc, hzc, hzA⟩
        obtain ⟨x, hxL, rfl⟩ := (hmemC c).1 hc
        refine ⟨?_, hzA⟩
        have h := L.add_mem (hΛL hzc) hxL
        simpa using h
    have hmeas : ∀ n, μ ((L : Set V) ∩ G ⁻¹' {z | z - T ∈ H n}) =
        ∑' p : C, μ ((p : Set V) ∩ G ⁻¹' {z | z - T ∈ H n}) := by
      intro n
      rw [hunion n]
      exact measure_biUnion hcount
        (fun c₁ h₁ c₂ h₂ hne => by
          change Disjoint (c₁ ∩ _) (c₂ ∩ _)
          exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left (hdisj h₁ h₂ hne))
        (fun c hc => by
          obtain ⟨x, -, rfl⟩ := (hmemC c).1 hc
          exact ((hcos_open x).inter (hAo n)).measurableSet)
    have hH0 : ν (H 0) ≠ 0 := (hHo 0).measure_ne_zero ν ⟨0, (H 0).zero_mem⟩
    have hH0' : ν (H 0) ≠ ⊤ := (hHc 0).measure_lt_top.ne
    have hcos : ∀ c ∈ C, ∀ n, μ (c ∩ G ⁻¹' {z | z - T ∈ H n}) * ν (H 0) =
        μ (c ∩ G ⁻¹' {z | z - T ∈ H 0}) * ν (H n) := by
      intro c hc n
      obtain ⟨x, hxL, rfl⟩ := (hmemC c).1 hc
      by_cases hex : ∃ y ∈ {z | z - x ∈ Λ 0}, G y - T ∈ H 0
      · obtain ⟨y, hy, hyT⟩ := hex
        have hyL : y ∈ L := by simpa using L.add_mem (hΛL hy) hxL
        rw [hsame x y hy]
        obtain ⟨D, hD, hG⟩ := hhens y hyL hyT
        have h0 := cos_ratio μ ν Λ H hΛo hΛa hHo hHc D hD G y hG T hyT 0
        have hn := cos_ratio μ ν Λ H hΛo hΛa hHo hHc D hD G y hG T hyT n
        rw [hn, eq_of_mul_mul_eq_of_det_ne_zero hH0 hH0' h0]
      · have e : ∀ m, {z | z - x ∈ Λ 0} ∩ G ⁻¹' {z | z - T ∈ H m} = ∅ := fun m =>
          Set.subset_empty_iff.1 fun z hz => hex ⟨z, hz.1, hHsub m hz.2⟩
        rw [e n, e 0]
        simp
    have hL : ∀ n, μ ((L : Set V) ∩ G ⁻¹' {z | z - T ∈ H n}) * ν (H 0) =
        μ ((L : Set V) ∩ G ⁻¹' {z | z - T ∈ H 0}) * ν (H n) := by
      intro n
      rw [hmeas n, hmeas 0, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right]
      exact tsum_congr fun p => hcos p.1 p.2 n
    refine fib_of_ratio μ ν f ι hι G hGc hfG U B fib hfib T hB Nb hNb hNbU (L : Set V) hLo hLcl hLc
      H hHo hHc hHb _ ?_
    intro n
    have h2 : μ ((L : Set V) ∩ G ⁻¹' {z | z - T ∈ H n}) =
        μ ((L : Set V) ∩ G ⁻¹' {z | z - T ∈ H 0}) / ν (H 0) * ν (H n) := by
      rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv, ENNReal.eq_div_iff hH0 hH0', mul_comm,
        hL n]
    rw [measureReal_def, measureReal_def, h2, ENNReal.toReal_mul]
  · push_neg at hgood
    have hTL : fib T (L : Set V) = 0 := by
      rw [← measure_inter_conull (hfib.1 T)]
      have e : (L : Set V) ∩ (f ⁻¹' {ι T} ∩ U) = ∅ := Set.subset_empty_iff.1 fun z hz => by
        have hGz : G z = T := hι ((hfG z).symm.trans (Set.mem_singleton_iff.1 hz.2.1))
        exact hgood z hz.1 (by rw [hGz, sub_self]; exact (H 0).zero_mem)
      rw [e, measure_empty]
    have hempty : (L : Set V) ∩ G ⁻¹' {z | z - T ∈ H 0} = ∅ :=
      Set.subset_empty_iff.1 fun z hz => hgood z hz.1 hz.2
    rw [integral_indicator hLo.measurableSet, Measure.restrict_eq_zero.2 hTL, integral_zero_measure,
      hempty]
    simp
end PI.VolStabSW
