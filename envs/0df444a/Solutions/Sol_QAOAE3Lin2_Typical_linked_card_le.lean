-- Prove2me | solution 1 for QAOAE3Lin2.Typical.linked_card_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:15:46.081987+00:00
-- url     : https://prove2.me/submissions/f9a711da-f631-48ac-ad59-8aa633514715

import Mathlib
import Definitions.Def_QAOAE3Lin2_Typical_Setting

namespace Aux_QAOAE3Lin2_linked_card_le
open QAOAE3Lin2.General

def bits {n : ℕ} (t : Fin n × Fin n × Fin n) : Finset (Fin n) := {t.1, t.2.1, t.2.2}

theorem on_iff {n : ℕ} (t : Fin n × Fin n × Fin n) (v : Fin n) : onTriple t v ↔ v ∈ bits t := by
  unfold onTriple bits; simp

theorem bits_card {n : ℕ} (t : Fin n × Fin n × Fin n) : (bits t).card ≤ 3 := by
  unfold bits
  exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
    (by simp)))

theorem role_mem {n : ℕ} (t : Fin n × Fin n × Fin n) (r : Fin 3) : roleBit t r ∈ bits t := by
  fin_cases r <;> simp [roleBit, bits]

end Aux_QAOAE3Lin2_linked_card_le

open QAOAE3Lin2.Typical QAOAE3Lin2.General Aux_QAOAE3Lin2_linked_card_le in
theorem solution {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (D : ℕ)
    (htri : QAOAE3Lin2.General.IsTripleFamily tri) (hocc : QAOAE3Lin2.General.BoundedOccurrence tri D) (i : Fin m) :
    (Finset.univ.filter fun i' => ¬ Disjoint (deps tri i) (deps tri i')).card ≤
      (6 * D + 3) * (D + 1) := by
  classical
  set rest := Finset.univ.filter fun j => ∃ r : Fin 3, sharesOnly tri i j r with hrest
  have hdeps : deps tri i = insert i rest := rfl
  have hirest : i ∉ rest := by
    intro h
    obtain ⟨r, hr⟩ := (Finset.mem_filter.mp h).2
    exact hr.1 rfl
  set B := bits (tri i) ∪ (deps tri i).biUnion (fun j => bits (tri j) \ bits (tri i)) with hB
  have hmemB : ∀ j ∈ deps tri i, ∀ v ∈ bits (tri j), v ∈ B := by
    intro j hj v hv
    by_cases hvi : v ∈ bits (tri i)
    · exact Finset.mem_union_left _ hvi
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_sdiff.mpr ⟨hv, hvi⟩⟩)
  have hcover : (Finset.univ.filter fun i' => ¬ Disjoint (deps tri i) (deps tri i')) ⊆
      B.biUnion (fun v => Finset.univ.filter fun i' => onTriple (tri i') v) := by
    intro i' hi'
    have hnd := (Finset.mem_filter.mp hi').2
    obtain ⟨j, hj1, hj2⟩ := Finset.not_disjoint_iff.mp hnd
    rw [Finset.mem_biUnion]
    rcases Finset.mem_insert.mp hj2 with h | h
    · subst h
      refine ⟨(tri j).1, hmemB j hj1 _ (by simp [bits]), ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩
    · obtain ⟨r, hr⟩ := (Finset.mem_filter.mp h).2
      refine ⟨roleBit (tri i') r, hmemB j hj1 _ ((on_iff _ _).mp hr.2.1), ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (on_iff _ _).mpr (role_mem _ r)⟩
  -- |rest| ≤ 3D
  have hrestcard : rest.card ≤ 3 * D := by
    have hsub : rest ⊆ (Finset.univ : Finset (Fin 3)).biUnion (fun r =>
        (Finset.univ.filter fun j => onTriple (tri j) (roleBit (tri i) r)).erase i) := by
      intro j hj
      obtain ⟨r, hr⟩ := (Finset.mem_filter.mp hj).2
      exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _,
        Finset.mem_erase.mpr ⟨hr.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.2.1⟩⟩⟩
    refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
    calc ∑ r : Fin 3, ((Finset.univ.filter fun j => onTriple (tri j) (roleBit (tri i) r)).erase i).card
        ≤ ∑ _r : Fin 3, D := by
          refine Finset.sum_le_sum fun r _ => ?_
          have hi : i ∈ Finset.univ.filter fun j => onTriple (tri j) (roleBit (tri i) r) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (on_iff _ _).mpr (role_mem _ r)⟩
          rw [Finset.card_erase_of_mem hi]
          have := hocc (roleBit (tri i) r)
          omega
      _ = 3 * D := by simp
  -- |B| ≤ 6D + 3
  have hBcard : B.card ≤ 6 * D + 3 := by
    have h1 : B.card ≤ (bits (tri i)).card +
        ∑ j ∈ deps tri i, (bits (tri j) \ bits (tri i)).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _)
    have h2 : ∑ j ∈ deps tri i, (bits (tri j) \ bits (tri i)).card ≤ 2 * rest.card := by
      rw [hdeps, Finset.sum_insert hirest, Finset.sdiff_self, Finset.card_empty, zero_add]
      calc ∑ j ∈ rest, (bits (tri j) \ bits (tri i)).card ≤ ∑ _j ∈ rest, 2 := by
            refine Finset.sum_le_sum fun j hj => ?_
            obtain ⟨r, hr⟩ := (Finset.mem_filter.mp hj).2
            have hv : roleBit (tri i) r ∈ bits (tri j) := (on_iff _ _).mp hr.2.1
            have hsub : bits (tri j) \ bits (tri i) ⊆ (bits (tri j)).erase (roleBit (tri i) r) := by
              intro v hv'
              obtain ⟨hv1, hv2⟩ := Finset.mem_sdiff.mp hv'
              refine Finset.mem_erase.mpr ⟨?_, hv1⟩
              rintro rfl; exact hv2 (role_mem _ r)
            have := Finset.card_le_card hsub
            rw [Finset.card_erase_of_mem hv] at this
            have := bits_card (tri j)
            omega
        _ = 2 * rest.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have h3 := bits_card (tri i)
    omega
  calc (Finset.univ.filter fun i' => ¬ Disjoint (deps tri i) (deps tri i')).card
      ≤ (B.biUnion (fun v => Finset.univ.filter fun i' => onTriple (tri i') v)).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ v ∈ B, (Finset.univ.filter fun i' => onTriple (tri i') v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ B, (D + 1) := Finset.sum_le_sum fun v _ => hocc v
    _ = B.card * (D + 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (6 * D + 3) * (D + 1) := Nat.mul_le_mul_right _ hBcard
