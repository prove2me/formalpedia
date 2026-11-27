-- Prove2me | solution 1 for PI.VolStabSW.measure_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:21:34.010401+00:00
-- url     : https://prove2.me/submissions/da74a935-2ca8-49ff-a567-e04313d06411

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensCntRes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace PI.VolStabSW
theorem _root_.solution {G V : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
    [AddCommGroup V] [Finite V] (μ : Measure G) [μ.IsAddLeftInvariant] (L N : AddSubgroup G)
    (hNL : N ≤ L) (hN : MeasurableSet (N : Set G)) (φ : G → V)
    (hadd : ∀ x ∈ L, ∀ y ∈ L, φ (x + y) = φ x + φ y) (hker : ∀ x ∈ L, φ x = 0 ↔ x ∈ N)
    (hsurj : ∀ w, ∃ x ∈ L, φ x = w) (S : Set V) :
    μ {x | x ∈ L ∧ φ x ∈ S} = (Nat.card S : ENNReal) * μ N := by
  classical
  haveI := Fintype.ofFinite V
  choose x hxL hxφ using hsurj
  have key : ∀ w y, -x w + y ∈ N → φ y = w := by
    intro w y hn
    have h1 := hadd _ (hxL w) _ (hNL hn)
    rw [add_neg_cancel_left, hxφ, (hker _ (hNL hn)).mpr hn, add_zero] at h1
    exact h1
  have hset : {y | y ∈ L ∧ φ y ∈ S} = ⋃ w ∈ S.toFinset, (fun h => -x w + h) ⁻¹' (N : Set G) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_toFinset, exists_prop, Set.mem_preimage,
      SetLike.mem_coe]
    constructor
    · rintro ⟨hy, hyS⟩
      refine ⟨φ y, hyS, ?_⟩
      have hmem : -x (φ y) + y ∈ L := L.add_mem (L.neg_mem (hxL _)) hy
      rw [← hker _ hmem]
      have h1 := hadd _ (hxL (φ y)) _ hmem
      rw [add_neg_cancel_left, hxφ] at h1
      calc φ (-x (φ y) + y) = -φ y + (φ y + φ (-x (φ y) + y)) := by abel
        _ = -φ y + φ y := by rw [← h1]
        _ = 0 := by abel
    · rintro ⟨w, hw, hn⟩
      have hyL : y ∈ L := by
        have h2 := L.add_mem (hxL w) (hNL hn)
        rwa [add_neg_cancel_left] at h2
      refine ⟨hyL, ?_⟩
      rw [key w y hn]
      exact hw
  rw [hset, MeasureTheory.measure_biUnion_finset]
  · simp only [MeasureTheory.measure_preimage_add]
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_card_toFinset]
  · intro w1 _ w2 _ hne
    exact Set.disjoint_left.mpr fun y h1 h2 => hne ((key w1 y h1).symm.trans (key w2 y h2))
  · intro w _
    exact (measurable_const_add (-x w)) hN
end PI.VolStabSW
