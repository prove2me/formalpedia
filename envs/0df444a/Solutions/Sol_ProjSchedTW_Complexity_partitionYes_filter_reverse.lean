-- Prove2me | solution 1 for ProjSchedTW.Complexity.partitionYes_filter_reverse
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T04:37:31.977703+00:00
-- url     : https://prove2.me/submissions/16620369-f6d5-4a43-b962-ce6dd2046c04

import Mathlib.Data.List.NodupEquivFin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fin.Rev
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_ProjSchedTW_Complexity_Encoding
open ProjSchedTW.Complexity
open scoped BigOperators

private theorem core {n m : ℕ} (f : Fin n ↪ Fin m) (a : Fin n → ℕ) (b : Fin m → ℕ)
    (hab : ∀ i, a i = b (f i)) (ht : (∑ i, a i) = ∑ j, b j) :
    (∃ A : Finset (Fin n), (∑ i ∈ A, a i) = ∑ i ∈ Aᶜ, a i) ↔
    (∃ B : Finset (Fin m), (∑ i ∈ B, b i) = ∑ i ∈ Bᶜ, b i) := by
  classical
  let R : Finset (Fin m) := Finset.univ.map f
  have hR : (∑ j ∈ R, b j) = ∑ j, b j := by
    simpa [R, Finset.sum_map, ← hab] using ht
  have hz : ∀ j, j ∉ R → b j = 0 := by
    intro j hj
    have hsum : (∑ j ∈ Rᶜ, b j) = 0 := by
      have h := Finset.sum_compl_add_sum R b
      omega
    have hmem : j ∈ Rᶜ := by simpa using hj
    exact Finset.sum_eq_zero_iff_of_nonneg (by intros; omega) |>.mp hsum j hmem
  have htotal (s : Finset (Fin m)) : (∑ j ∈ s, b j) = ∑ j ∈ s ∩ R, b j := by
    symm
    apply Finset.sum_subset (Finset.inter_subset_left)
    intro x hx hnot
    apply hz
    intro hxr
    exact hnot (Finset.mem_inter.mpr ⟨hx, hxr⟩)
  have hm (s : Finset (Fin m)) : ((s.preimage f f.injective.injOn).map f) = s ∩ R := by
    ext j
    simp [R, Finset.mem_map, Finset.mem_preimage, and_comm]
    aesop
  have hsum (s : Finset (Fin m)) : (∑ i ∈ s.preimage f f.injective.injOn, a i) = ∑ j ∈ s, b j := by
    calc
      _ = ∑ j ∈ (s.preimage f f.injective.injOn).map f, b j := by simp [Finset.sum_map, hab]
      _ = _ := by rw [hm, ← htotal]
  have chara (A : Finset (Fin n)) : (∑ i ∈ A, a i) = (∑ i ∈ Aᶜ, a i) ↔ 2 * (∑ i ∈ A, a i) = ∑ i, a i := by
    have h := Finset.sum_compl_add_sum A a
    omega
  have charb (B : Finset (Fin m)) : (∑ i ∈ B, b i) = (∑ i ∈ Bᶜ, b i) ↔ 2 * (∑ i ∈ B, b i) = ∑ i, b i := by
    have h := Finset.sum_compl_add_sum B b
    omega
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨A.map f, charb _ |>.2 ?_⟩
    have h := (chara A).1 hA
    simpa [Finset.sum_map, ← hab, ← ht] using h
  · rintro ⟨B, hB⟩
    refine ⟨B.preimage f f.injective.injOn, chara _ |>.2 ?_⟩
    rw [hsum, ht]
    exact (charb B).1 hB

private theorem sub_inv (l l' : List ℕ) (h : List.Sublist l l') (hs : l.sum = l'.sum) : PartitionYes l ↔ PartitionYes l' := by
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp h
  apply core f.toEmbedding l.get l'.get hf
  simpa [List.sum_ofFn] using hs

theorem solution (xs : List ℕ) : PartitionYes xs ↔ PartitionYes ((xs.filter (fun a => a ≠ 0)).reverse) := by
  have hf : PartitionYes (xs.filter (fun a => a ≠ 0)) ↔ PartitionYes xs := by
    apply sub_inv _ _ List.filter_sublist
    induction xs with
    | nil => simp
    | cons x xs ih => by_cases hx : x = 0 <;> simp_all
  have hr : PartitionYes (xs.filter (fun a => a ≠ 0)) ↔ PartitionYes ((xs.filter (fun a => a ≠ 0)).reverse) := by
    let l := xs.filter (fun a => a ≠ 0)
    have he : (∀ i : Fin l.length, l.get i = l.reverse.get ((Fin.cast (show l.reverse.length = l.length from List.length_reverse).symm i.rev))) := by
      intro i
      simp
      congr 1
      omega
    apply core ((Fin.revPerm (n := l.length)).toEmbedding.trans (Fin.castLEEmb (by simp))) l.get l.reverse.get ?_ ?_
    · exact he
    · simpa only [← List.sum_ofFn, List.ofFn_get] using (List.sum_reverse l).symm
  exact hf.symm.trans hr