-- Prove2me | solution 1 for PI.VolStabW.hensel_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:56:53.748653+00:00
-- url     : https://prove2.me/submissions/9ac3f495-499a-491e-b727-cea6a8ef1fdb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_HenselCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_HenselCountHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Topology
variable {V X : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
namespace PI.VolStabW
theorem _root_.solution (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set V))
    (hΛa : Antitone Λ) (hHo : ∀ n, IsOpen (H n : Set X)) (hHc : ∀ n, IsCompact (H n : Set X))
    (D : V →+ X) (hD : ∀ n, (Λ n).map D = H n) (G : V → X) (y : V)
    (hG : ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1))
    (h : X) (hh : h - G y ∈ H 0) (n : ℕ) :
    μ (hlev (Λ 0) (H n) G y h) * ν (H 0) = μ (Λ 0) * ν (H n) := by
  have hHa : ∀ n, H (n + 1) ≤ H n := by
    intro n
    rw [← hD, ← hD]
    exact AddSubgroup.map_mono (hΛa (Nat.le_succ n))
  have hDW : ∀ n W, W ∈ Λ n → D W ∈ H n := fun n W hW => hD n ▸ AddSubgroup.mem_map_of_mem D hW
  have hΛ0 : ∀ n W, W ∈ Λ n → W ∈ Λ 0 := fun n W hW => hΛa (Nat.zero_le n) hW

  have hopen : ∀ m h', IsOpen (hlev (Λ 0) (H m) G y h') := by
    intro m h'
    rw [isOpen_iff_forall_mem_open]
    rintro Z ⟨hZ0, hZh⟩
    refine ⟨{x | x - Z ∈ Λ m}, ?_, (hΛo m).preimage (continuous_id.sub continuous_const),
      by simp [(Λ m).zero_mem]⟩
    intro x hx
    have hx : x - Z ∈ Λ m := hx
    have hx' : x = Z + (x - Z) := by abel
    refine ⟨?_, ?_⟩
    · rw [hx']
      exact (Λ 0).add_mem hZ0 (hΛ0 m _ hx)
    · have h1 := hG m Z hZ0 (x - Z) hx
      have h2 := hDW m _ hx
      have e : G (y + x) - h' = (G (y + Z + (x - Z)) - G (y + Z) - D (x - Z)) + D (x - Z) +
          (G (y + Z) - h') := by
        rw [show y + Z + (x - Z) = y + x by abel]
        abel
      rw [e]
      exact (H m).add_mem ((H m).add_mem (hHa m h1) h2) hZh

  have htr : ∀ n h' W, W ∈ Λ n →
      μ (hlev (Λ 0) (H (n + 1)) G y (h' + D W)) = μ (hlev (Λ 0) (H (n + 1)) G y h') := by
    intro n h' W hW
    have hW0 := hΛ0 n W hW
    have e : hlev (Λ 0) (H (n + 1)) G y (h' + D W) =
        (fun Z => -W + Z) ⁻¹' hlev (Λ 0) (H (n + 1)) G y h' := by
      ext Z
      simp only [hlev, Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hZ, hZh⟩
        have hZ' : -W + Z ∈ Λ 0 := (Λ 0).add_mem ((Λ 0).neg_mem hW0) hZ
        refine ⟨hZ', ?_⟩
        have h1 := hG n (-W + Z) hZ' W hW
        rw [show y + (-W + Z) + W = y + Z by abel] at h1
        have e2 : G (y + (-W + Z)) - h' =
            (G (y + Z) - (h' + D W)) - (G (y + Z) - G (y + (-W + Z)) - D W) := by abel
        rw [e2]
        exact (H (n + 1)).sub_mem hZh h1
      · rintro ⟨hZ', hZh⟩
        have hZ : Z ∈ Λ 0 := by
          have := (Λ 0).add_mem hW0 hZ'
          rwa [add_neg_cancel_left] at this
        refine ⟨hZ, ?_⟩
        have h1 := hG n (-W + Z) hZ' W hW
        rw [show y + (-W + Z) + W = y + Z by abel] at h1
        have e2 : G (y + Z) - (h' + D W) =
            (G (y + Z) - G (y + (-W + Z)) - D W) + (G (y + (-W + Z)) - h') := by abel
        rw [e2]
        exact (H (n + 1)).add_mem h1 hZh
    rw [e, measure_preimage_add]

  have hstep : ∀ n, ∃ k : ℕ, k ≠ 0 ∧
      μ (hlev (Λ 0) (H n) G y h) = k * μ (hlev (Λ 0) (H (n + 1)) G y h) ∧
      ν (H n) = k * ν (H (n + 1)) := by
    intro n
    have : DiscreteTopology (X ⧸ H (n + 1)) := QuotientAddGroup.discreteTopology (hHo (n + 1))
    let q : X → X ⧸ H (n + 1) := QuotientAddGroup.mk
    have hq : Continuous q := continuous_quot_mk
    have hfin : (q '' (H n : Set X)).Finite := ((hHc n).image hq).finite_of_discrete
    set T := hfin.toFinset with hT
    have hqeq : ∀ a b, q a = q b ↔ a - b ∈ H (n + 1) := fun a b => QuotientAddGroup.eq_iff_sub_mem
    have hmemT : ∀ p, p ∈ T ↔ ∃ u ∈ H n, q u = p := by
      intro p
      simp [hT, q]
    let piece : X ⧸ H (n + 1) → Set V := fun p => {Z | Z ∈ Λ 0 ∧ q (G (y + Z) - h) = p}
    have hpiece : ∀ u, piece (q u) = hlev (Λ 0) (H (n + 1)) G y (h + u) := by
      intro u
      ext Z
      simp only [piece, hlev, Set.mem_setOf_eq, hqeq, sub_sub]
    have hA : hlev (Λ 0) (H n) G y h = ⋃ p ∈ T, piece p := by
      ext Z
      simp only [Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨hZ, hZh⟩
        exact ⟨q (G (y + Z) - h), (hmemT _).2 ⟨_, hZh, rfl⟩, hZ, rfl⟩
      · rintro ⟨p, hp, hZ, hZp⟩
        obtain ⟨u, hu, rfl⟩ := (hmemT p).1 hp
        refine ⟨hZ, ?_⟩
        have h1 := (hqeq _ _).1 hZp
        have e : G (y + Z) - h = (G (y + Z) - h - u) + u := by abel
        rw [e]
        exact (H n).add_mem (hHa n h1) hu
    have hdisj : Set.PairwiseDisjoint (↑T : Set (X ⧸ H (n + 1))) piece := by
      intro p _ p' _ hne
      refine Set.disjoint_left.2 fun Z hZ hZ' => hne ?_
      exact hZ.2.symm.trans hZ'.2
    have hmeasP : ∀ p ∈ T, MeasurableSet (piece p) := by
      intro p hp
      obtain ⟨u, _, rfl⟩ := (hmemT p).1 hp
      rw [hpiece]
      exact (hopen _ _).measurableSet
    have hvalP : ∀ p ∈ T, μ (piece p) = μ (hlev (Λ 0) (H (n + 1)) G y h) := by
      intro p hp
      obtain ⟨u, hu, rfl⟩ := (hmemT p).1 hp
      rw [hpiece]
      rw [← hD n] at hu
      obtain ⟨W, hW, rfl⟩ := AddSubgroup.mem_map.1 hu
      exact htr n h W hW
    have hH : (H n : Set X) = ⋃ p ∈ T, q ⁻¹' {p} := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, exists_prop]
      constructor
      · intro hx
        exact ⟨q x, (hmemT _).2 ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨p, hp, hxp⟩
        obtain ⟨u, hu, rfl⟩ := (hmemT p).1 hp
        have h1 := (hqeq _ _).1 hxp
        have e : x = (x - u) + u := by abel
        rw [e]
        exact (H n).add_mem (hHa n h1) hu
    have hdisjH : Set.PairwiseDisjoint (↑T : Set (X ⧸ H (n + 1))) (fun p => q ⁻¹' {p}) :=
      fun p _ p' _ hne => (Set.disjoint_singleton.2 hne).preimage q
    have hmeasH : ∀ p ∈ T, MeasurableSet (q ⁻¹' {p}) := fun p _ =>
      ((isOpen_discrete ({p} : Set (X ⧸ H (n + 1)))).preimage hq).measurableSet
    have hvalH : ∀ p ∈ T, ν (q ⁻¹' {p}) = ν (H (n + 1)) := by
      intro p hp
      obtain ⟨u, _, rfl⟩ := (hmemT p).1 hp
      have e : q ⁻¹' {q u} = (fun z => -u + z) ⁻¹' (H (n + 1) : Set X) := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff, hqeq, SetLike.mem_coe]
        rw [show z - u = -u + z by abel]
      rw [e, measure_preimage_add]
    refine ⟨T.card, ?_, ?_, ?_⟩
    · refine Finset.card_ne_zero.2 ⟨q 0, (hmemT _).2 ⟨0, (H n).zero_mem, rfl⟩⟩
    · rw [hA, measure_biUnion_finset hdisj hmeasP, Finset.sum_congr rfl hvalP, Finset.sum_const,
        nsmul_eq_mul]
    · rw [hH, measure_biUnion_finset hdisjH hmeasH, Finset.sum_congr rfl hvalH, Finset.sum_const,
        nsmul_eq_mul]
  induction n with
  | zero =>
    have e : hlev (Λ 0) (H 0) G y h = (Λ 0 : Set V) := by
      ext Z
      simp only [hlev, Set.mem_setOf_eq, SetLike.mem_coe, and_iff_left_iff_imp]
      intro hZ
      have h1 := hG 0 0 (Λ 0).zero_mem Z hZ
      simp only [add_zero] at h1
      have e2 : G (y + Z) - h = (G (y + Z) - G y - D Z) + D Z - (h - G y) := by abel
      rw [e2]
      exact (H 0).sub_mem ((H 0).add_mem (hHa 0 h1) (hDW 0 Z hZ)) hh
    rw [e, mul_comm]
  | succ n ih =>
    obtain ⟨k, hk, hμ, hν⟩ := hstep n
    have hk0 : (k : ENNReal) ≠ 0 := Nat.cast_ne_zero.2 hk
    have key : (k : ENNReal) * (μ (hlev (Λ 0) (H (n + 1)) G y h) * ν (H 0)) =
        k * (μ (Λ 0) * ν (H (n + 1))) := by
      rw [← mul_assoc, ← hμ, ih, hν]
      ring
    exact (ENNReal.mul_right_inj hk0 (ENNReal.natCast_ne_top k)).1 key
end PI.VolStabW
