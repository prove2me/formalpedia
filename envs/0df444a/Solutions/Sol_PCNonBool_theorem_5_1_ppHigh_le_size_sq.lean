-- Prove2me | solution 1 for PCNonBool.theorem_5_1_ppHigh_le_size_sq
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:17:02.008213+00:00
-- url     : https://prove2.me/submissions/f961deed-97cb-4d19-a86d-1f14e089bcda

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_pcSize
import Definitions.Def_PCNonBool_ppHighOn

open PCNonBool in
theorem solution {F : Type*} [Field F] {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (G : BipGraph U V) (Ua : Finset U) (Va : Finset V) (D : ℝ)
    (π : List (MvPolynomial (Var G) F)) :
    (ppHighOn G Ua Va D π).card ≤ pcSize π ^ 2 := by
  classical
  have hsub : ppHighOn G Ua Va D π ⊆ π.toFinset.biUnion (fun p => qset p) := by
    intro q hq
    unfold ppHighOn at hq
    rw [Finset.mem_biUnion] at hq ⊢
    obtain ⟨p, hp, hq'⟩ := hq
    exact ⟨p, List.mem_toFinset.mpr (List.mem_toFinset.mp hp), (Finset.mem_filter.mp hq').1⟩
  have hS : ∑ p ∈ π.toFinset, p.support.card ≤ pcSize π := by
    unfold pcSize
    rw [Finset.sum_list_map_count]
    apply Finset.sum_le_sum
    intro p hp
    rw [smul_eq_mul]
    have h1 : 0 < π.count p := List.count_pos_iff.mpr (List.mem_toFinset.mp hp)
    exact Nat.le_mul_of_pos_left _ h1
  have hq : ∀ p ∈ π.toFinset, (qset p).card ≤ p.support.card * pcSize π := by
    intro p hp
    have hs1 : p.support.card ≤ pcSize π :=
      le_trans (Finset.single_le_sum (f := fun p : MvPolynomial (Var G) F => p.support.card)
        (fun _ _ => Nat.zero_le _) hp) hS
    have hs2 : (qset p).card ≤ p.support.card * p.support.card := by
      unfold qset
      rw [Finset.card_sym2, Nat.choose_two_right, Nat.add_sub_cancel]
      apply Nat.div_le_of_le_mul
      nlinarith
    exact le_trans hs2 (Nat.mul_le_mul_left _ hs1)
  calc (ppHighOn G Ua Va D π).card ≤ (π.toFinset.biUnion (fun p => qset p)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ π.toFinset, (qset p).card := Finset.card_biUnion_le
    _ ≤ ∑ p ∈ π.toFinset, p.support.card * pcSize π := Finset.sum_le_sum hq
    _ = (∑ p ∈ π.toFinset, p.support.card) * pcSize π := (Finset.sum_mul _ _ _).symm
    _ ≤ pcSize π * pcSize π := Nat.mul_le_mul_right _ hS
    _ = pcSize π ^ 2 := (sq _).symm
