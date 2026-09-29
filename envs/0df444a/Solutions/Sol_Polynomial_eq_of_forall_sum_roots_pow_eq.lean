-- Prove2me | solution 1 for Polynomial.eq_of_forall_sum_roots_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/b622eec5-de1f-588c-a9ae-9d9b2d8e2bea

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_eq_of_forall_sum_roots_pow_eq

set_option autoImplicit false

namespace P2mPowSum

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in

theorem sum_map_pow_eq_sum [DecidableEq K] (s : Multiset K) (U : Finset K) (hU : s.toFinset ⊆ U)
    (n : ℕ) : (s.map fun z => z ^ n).sum = ∑ u ∈ U, (s.count u : K) * u ^ n := by
  rw [Finset.sum_multiset_map_count]
  rw [Finset.sum_subset hU]
  · apply Finset.sum_congr rfl
    intro u _
    rw [nsmul_eq_mul]
  · intro u _ hu
    rw [Multiset.mem_toFinset] at hu
    rw [Multiset.count_eq_zero_of_notMem hu, zero_smul]

omit [Field K] [CharZero K] in

theorem card_eq_sum_count [DecidableEq K] (s : Multiset K) (U : Finset K) (hU : s.toFinset ⊆ U) :
    Multiset.card s = ∑ u ∈ U, s.count u := by
  rw [← Multiset.toFinset_sum_count_eq s]
  rw [Finset.sum_subset hU]
  intro u _ hu
  rw [Multiset.mem_toFinset] at hu
  exact Multiset.count_eq_zero_of_notMem hu

theorem multiset_eq_of_forall_sum_pow_eq (s t : Multiset K) (hcard : Multiset.card s = Multiset.card t)
    (h : ∀ n : ℕ, 0 < n → (s.map fun z => z ^ n).sum = (t.map fun z => z ^ n).sum) :
    s = t := by
  classical
  set U : Finset K := s.toFinset ∪ t.toFinset with hUdef
  have hsU : s.toFinset ⊆ U := Finset.subset_union_left
  have htU : t.toFinset ⊆ U := Finset.subset_union_right
  set N := U.card with hN
  set e : Fin N ≃ U := U.equivFin.symm with he
  set f : Fin N → K := fun i => (e i : K) with hf
  have hfinj : Function.Injective f := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  set w : K → K := fun u => (s.count u : K) - (t.count u : K) with hw
  set v : Fin N → K := fun j => w (f j) * f j with hv

  have hsys : ∀ i : Fin N, (∑ j : Fin N, v j * f j ^ (i : ℕ)) = 0 := by
    intro i
    have h1 : (∑ j : Fin N, v j * f j ^ (i : ℕ)) = ∑ u ∈ U, w u * u ^ ((i : ℕ) + 1) := by
      rw [← Finset.sum_coe_sort U]
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro j _
      simp only [hv, hf]
      ring
    rw [h1]
    have h2 : ∑ u ∈ U, w u * u ^ ((i : ℕ) + 1) =
        (∑ u ∈ U, (s.count u : K) * u ^ ((i : ℕ) + 1)) -
          ∑ u ∈ U, (t.count u : K) * u ^ ((i : ℕ) + 1) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro u _
      simp only [hw]
      ring
    rw [h2, ← sum_map_pow_eq_sum s U hsU, ← sum_map_pow_eq_sum t U htU, h _ (Nat.succ_pos _),
      sub_self]
  have hv0 : v = 0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hfinj hsys

  have hcount : ∀ u : K, u ≠ 0 → s.count u = t.count u := by
    intro u hu0
    by_cases huU : u ∈ U
    · have hj := congr_fun hv0 (e.symm ⟨u, huU⟩)
      simp only [hv, hf, Equiv.apply_symm_apply, Pi.zero_apply, mul_eq_zero] at hj
      rcases hj with hj | hj
      · simp only [hw, sub_eq_zero] at hj
        exact_mod_cast hj
      · exact absurd hj hu0
    · have hus : u ∉ s := fun h' => huU (hsU (Multiset.mem_toFinset.mpr h'))
      have hut : u ∉ t := fun h' => huU (htU (Multiset.mem_toFinset.mpr h'))
      rw [Multiset.count_eq_zero_of_notMem hus, Multiset.count_eq_zero_of_notMem hut]

  have hcount0 : s.count 0 = t.count 0 := by
    set U' : Finset K := insert 0 U with hU'
    have h0 : (0 : K) ∈ U' := Finset.mem_insert_self 0 U
    have hs := card_eq_sum_count s U' (hsU.trans (Finset.subset_insert _ _))
    have ht := card_eq_sum_count t U' (htU.trans (Finset.subset_insert _ _))
    rw [← Finset.add_sum_erase U' _ h0] at hs ht
    have hrest : ∑ x ∈ U'.erase 0, s.count x = ∑ x ∈ U'.erase 0, t.count x := by
      apply Finset.sum_congr rfl
      intro u hu
      exact hcount u (Finset.ne_of_mem_erase hu)
    rw [hrest, hcard, ht] at hs
    omega
  ext u
  by_cases hu : u = 0
  · rw [hu]; exact hcount0
  · exact hcount u hu

theorem poly_eq (P Q : K[X]) (hP : P.Monic) (hQ : Q.Monic) (hPs : P.Splits) (hQs : Q.Splits)
    (hdeg : P.natDegree = Q.natDegree)
    (h : ∀ n : ℕ, 0 < n → (P.roots.map fun z => z ^ n).sum = (Q.roots.map fun z => z ^ n).sum) :
    P = Q := by
  have hcard : Multiset.card P.roots = Multiset.card Q.roots := by
    rw [← hPs.natDegree_eq_card_roots, ← hQs.natDegree_eq_card_roots, hdeg]
  have hroots := multiset_eq_of_forall_sum_pow_eq P.roots Q.roots hcard h
  rw [hPs.eq_prod_roots_of_monic hP, hQs.eq_prod_roots_of_monic hQ, hroots]

end P2mPowSum

theorem solution {K : Type*} [Field K] [CharZero K]
    (P Q : Polynomial K) (hP : P.Monic) (hQ : Q.Monic) (hPs : P.Splits) (hQs : Q.Splits)
    (hdeg : P.natDegree = Q.natDegree)
    (h : ∀ n : ℕ, 0 < n →
      (P.roots.map (fun z => z ^ n)).sum = (Q.roots.map (fun z => z ^ n)).sum) :
    P = Q :=
  P2mPowSum.poly_eq P Q hP hQ hPs hQs hdeg h

end S_Polynomial_eq_of_forall_sum_roots_pow_eq
end P2MW
export P2MW.S_Polynomial_eq_of_forall_sum_roots_pow_eq (solution)
