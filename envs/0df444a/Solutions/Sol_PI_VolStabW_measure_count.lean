-- Prove2me | solution 1 for PI.VolStabW.measure_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:17:28.832904+00:00
-- url     : https://prove2.me/submissions/90b15ee3-f2a2-418c-9a47-c6d80d848a3f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntRes

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
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace PI.VolStabW
theorem _root_.solution {G V : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
    [AddCommGroup V] [Finite V] (μ : Measure G) [μ.IsAddLeftInvariant] (L N : AddSubgroup G)
    (hNL : N ≤ L) (hN : MeasurableSet (N : Set G)) (φ : G → V)
    (hadd : ∀ x ∈ L, ∀ y ∈ L, φ (x + y) = φ x + φ y) (hker : ∀ x ∈ L, φ x = 0 ↔ x ∈ N)
    (hsurj : ∀ w, ∃ x ∈ L, φ x = w) (S : Set V) :
    μ {x | x ∈ L ∧ φ x ∈ S} = (Nat.card S : ENNReal) * μ N := by
  choose l hlL hl using hsurj
  have key : ∀ s x, -l s + x ∈ N ↔ x ∈ L ∧ φ x = s := by
    intro s x
    constructor
    · intro h
      have hx : x = l s + (-l s + x) := by abel
      have hL : x ∈ L := by rw [hx]; exact L.add_mem (hlL s) (hNL h)
      refine ⟨hL, ?_⟩
      rw [hx, hadd _ (hlL s) _ (hNL h), hl, (hker _ (hNL h)).2 h, add_zero]
    · rintro ⟨hL, rfl⟩
      have hm : -l (φ x) + x ∈ L := L.add_mem (L.neg_mem (hlL _)) hL
      refine (hker _ hm).1 ?_
      have e := hadd _ (hlL (φ x)) _ hm
      rw [show l (φ x) + (-l (φ x) + x) = x by abel, hl] at e
      have e2 := e.symm
      rwa [add_eq_left] at e2
  have hfin : S.Finite := S.toFinite
  have hset : {x | x ∈ L ∧ φ x ∈ S} =
      ⋃ s ∈ hfin.toFinset, (fun x => -l s + x) ⁻¹' (N : Set G) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe,
      Set.Finite.mem_toFinset, exists_prop, key]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨_, h2, h1, rfl⟩
    · rintro ⟨s, hs, h1, rfl⟩; exact ⟨h1, hs⟩
  rw [hset, measure_biUnion_finset]
  · simp only [measure_preimage_add]
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_card_finite_toFinset hfin]
  · intro s _ t _ hst
    refine Set.disjoint_left.2 fun x h1 h2 => hst ?_
    simp only [Set.mem_preimage, SetLike.mem_coe, key] at h1 h2
    rw [← h1.2, ← h2.2]
  · intro s _
    exact hN.preimage (measurable_const_add _)
end PI.VolStabW
