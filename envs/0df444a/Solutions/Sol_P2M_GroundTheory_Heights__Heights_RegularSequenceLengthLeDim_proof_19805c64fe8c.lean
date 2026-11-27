-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegularSequenceLengthLeDim_proof_19805c64fe8c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:08:25.814726+00:00
-- url     : https://prove2.me/submissions/2a7c27f3-643b-4e1b-9db5-926e75e0ac97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularSequenceLengthLeDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularSequenceLengthLeDim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing RingTheory.Sequence Pointwise
universe u
namespace GroundTheory.Heights₂.Heights
namespace RegularSequenceLengthLeDim
theorem _root_.solution : RegularSequenceLengthLeDim.Statement.{u} := by
  suffices key : ∀ (n : ℕ) (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (rs : List R),
      rs.length = n → (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs →
        (rs.length : WithBot ℕ∞) ≤ ringKrullDim R from
    fun R _ _ _ rs hmem hreg => key _ R rs rfl hmem hreg
  intro n
  induction n with
  | zero =>
    intro R _ _ _ rs hlen _ _
    rw [hlen, Nat.cast_zero]
    exact ringKrullDim_nonneg_of_nontrivial
  | succ n ih =>
    intro R _ _ _ rs hlen hmem hreg
    obtain _ | ⟨r, rs⟩ := rs
    · simp at hlen
    rw [List.length_cons, Nat.succ_inj] at hlen
    rw [isWeaklyRegular_cons_iff] at hreg
    obtain ⟨hr, htail⟩ := hreg
    have hrm : r ∈ maximalIdeal R := hmem r (List.mem_cons_self ..)
    set S := R ⧸ Ideal.span {r}
    have hne : Ideal.span {r} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]
      exact (mem_maximalIdeal _).mp hrm
    have : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing S := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {r})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hdim : ringKrullDim S + 1 = ringKrullDim R :=
      ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hr hrm
    have heq : (r • ⊤ : Submodule R R) = Ideal.span {r} := by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
    have hS : IsWeaklyRegular S rs :=
      (Submodule.quotEquivOfEq _ _ heq).isWeaklyRegular_congr rs |>.mp htail
    have hS' : IsWeaklyRegular S (rs.map (algebraMap R S)) :=
      (isWeaklyRegular_map_algebraMap_iff S S rs).mpr hS
    have hmem' : ∀ s ∈ rs.map (algebraMap R S), s ∈ maximalIdeal S := by
      intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      refine (mem_maximalIdeal _).mpr fun hu => (mem_maximalIdeal _).mp (hmem t (List.mem_cons_of_mem _ ht)) ?_
      exact isUnit_of_map_unit (Ideal.Quotient.mk (Ideal.span {r})) t hu
    have h := ih S _ (by rw [List.length_map, hlen]) hmem' hS'
    rw [List.length_map] at h
    rw [← hdim, List.length_cons, Nat.cast_succ]
    exact add_le_add h le_rfl
end RegularSequenceLengthLeDim
end GroundTheory.Heights₂.Heights
