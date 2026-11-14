-- Prove2me | solution 1 for SaglamGV.circuit_sum_rank
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-13T11:12:57.954248+00:00
-- url     : https://prove2.me/submissions/fbb54311-45fa-4371-a8b0-2d43cf843187

import Definitions.Def_SaglamGV_Circuit
set_option autoImplicit false
open Finset Submodule

private lemma circuit_sum {n : ℕ} (S : Finset (Fin n → ZMod 2))
    (hS : SaglamGV.IsCircuit S) : ∑ x ∈ S, x = 0 := by
  classical
  obtain ⟨g, hg, y, hy, hgy⟩ :=
    (not_linearIndepOn_finset_iff (R := ZMod 2) (v := id) (s := S)).mp hS.1
  change (∑ x ∈ S, g x • x) = 0 at hg
  have hg1 (x : Fin n → ZMod 2) (hx : x ∈ S) : g x = 1 := by
    have hnon : g x ≠ 0 := by
      intro hx0
      have hLI := hS.2 (S.erase x) (Finset.erase_ssubset hx)
      have hsum : ∑ u ∈ S.erase x, g u • u = 0 := by
        rw [Finset.sum_erase_eq_sub hx, hg, hx0, zero_smul, sub_zero]
      have hyx : y ≠ x := by rintro rfl; exact hgy hx0
      exact hgy (((linearIndepOn_finset_iff (R := ZMod 2) (v := id)
        (s := S.erase x)).mp hLI) g hsum y (mem_erase.mpr ⟨hyx, hy⟩))
    exact (show ∀ a : ZMod 2, a ≠ 0 → a = 1 by decide) (g x) hnon
  calc
    ∑ x ∈ S, x = ∑ x ∈ S, g x • x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hg1 x hx, one_smul]
    _ = 0 := hg

private lemma circuit_rank {n : ℕ} (S : Finset (Fin n → ZMod 2))
    (hS : SaglamGV.IsCircuit S) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (S : Set (Fin n → ZMod 2))) =
      S.card - 1 := by
  classical
  have hne : S.Nonempty := by
    by_contra h
    have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst S
    exact hS.1 (by simp)
  obtain ⟨x, hx⟩ := hne
  have hLI := hS.2 (S.erase x) (Finset.erase_ssubset hx)
  have hsum := circuit_sum S hS
  have hxeq : x = - ∑ y ∈ S.erase x, y := by
    have h := Finset.sum_erase_add S (fun y ↦ y) hx
    rw [hsum] at h
    exact eq_neg_of_add_eq_zero_right h
  have hxspan : x ∈ Submodule.span (ZMod 2) (S.erase x : Set (Fin n → ZMod 2)) := by
    have hmem : -∑ y ∈ S.erase x, y ∈
        Submodule.span (ZMod 2) (S.erase x : Set (Fin n → ZMod 2)) := by
      apply Submodule.neg_mem
      exact Submodule.sum_mem _ (fun y hy ↦ Submodule.subset_span hy)
    rwa [← hxeq] at hmem
  have hsp : Submodule.span (ZMod 2) (S : Set (Fin n → ZMod 2)) =
      Submodule.span (ZMod 2) (S.erase x : Set (Fin n → ZMod 2)) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      intro y hy
      by_cases hxy : y = x
      · simpa [hxy] using hxspan
      · exact Submodule.subset_span (Finset.mem_erase.mpr ⟨hxy, hy⟩)
    · exact Submodule.span_mono (by intro y hy; exact Finset.mem_of_mem_erase hy)
  rw [hsp, finrank_span_finset_eq_card hLI, Finset.card_erase_of_mem hx]


theorem solution (n d ℓ : ℕ) (S : Finset (Fin n → ZMod 2))
    (hS : S ∈ SaglamGV.circuits n d ℓ) :
    ∑ x ∈ S, x = 0 ∧
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (S : Set (Fin n → ZMod 2))) = ℓ - 1 ∧
      3 ≤ ℓ ∧ ℓ ≤ n + 1 := by
  classical
  simp only [SaglamGV.circuits, SaglamGV.allCircuits, Finset.mem_filter,
    Finset.mem_powerset] at hS
  obtain ⟨⟨hsub, hcirc⟩, hcard⟩ := hS
  have hsum := circuit_sum S hcirc
  have hrank := circuit_rank S hcirc
  have hzero : (0 : Fin n → ZMod 2) ∉ S := by
    intro h0
    have := (Finset.mem_filter.mp (hsub h0)).2.1
    simp at this
  have hpos : 0 < S.card := by
    by_contra h
    have he : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst S
    exact hcirc.1 (by simp)
  have hthree : 3 ≤ S.card := by
    by_contra h
    have hone_two : S.card = 1 ∨ S.card = 2 := by omega
    rcases hone_two with hone | htwo
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hone
      have hx : x = 0 := by simpa using hsum
      exact hzero (by simp [hx])
    · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp htwo
      have hadd : x + y = 0 := by simpa [hxy] using hsum
      have hyx : y = -x := eq_neg_of_add_eq_zero_right hadd
      have hneg : -x = x := by
        ext i
        exact CharTwo.neg_eq (x i)
      rw [hneg] at hyx
      exact hxy hyx.symm
  refine ⟨hsum, ?_, ?_, ?_⟩
  · simpa [hcard] using hrank
  · omega
  · have hdim := (Submodule.span (ZMod 2) (S : Set (Fin n → ZMod 2))).finrank_le
    rw [Module.finrank_pi, Fintype.card_fin] at hdim
    omega
