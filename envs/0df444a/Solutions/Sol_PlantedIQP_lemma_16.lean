-- Prove2me | solution 1 for PlantedIQP.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:52:08.933204+00:00
-- url     : https://prove2.me/submissions/160e4c46-aaa1-4a05-a06a-d810a4cc16ce

import Mathlib
import Definitions.Def_PlantedIQP_triForm

set_option autoImplicit false

namespace Aux_PIQ16

open PlantedIQP

variable {n : ℕ}

theorem id3 : ∀ ua ub uc va vb vc wa wb wc : ZMod 2,
    (ua + va + wa) * (ub + vb + wb) * (uc + vc + wc) + (ua + va) * (ub + vb) * (uc + vc) +
      (va + wa) * (vb + wb) * (vc + wc) + (ua + wa) * (ub + wb) * (uc + wc) +
      ua * ub * uc + va * vb * vc + wa * wb * wc =
    ua * vb * wc + ua * vc * wb + ub * va * wc + ub * vc * wa + uc * va * wb + uc * vb * wa := by
  decide

theorem id2 : ∀ ua ub va vb wa wb : ZMod 2,
    (ua + va + wa) * (ub + vb + wb) + (ua + va) * (ub + vb) + (va + wa) * (vb + wb) +
      (ua + wa) * (ub + wb) + ua * ub + va * vb + wa * wb = 0 := by
  decide

theorem id1 : ∀ a b c : ZMod 2, (a + b + c) + (a + b) + (b + c) + (a + c) + a + b + c = 0 := by
  decide

theorem distinct_of_card (i j k : Fin n) (h : ({i, j, k} : Finset (Fin n)).card = 3) :
    i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  refine ⟨?_, ?_, ?_⟩
  · intro e; subst e
    rw [Finset.insert_eq_of_mem (Finset.mem_insert_self _ _)] at h
    have := Finset.card_le_two (a := i) (b := k); omega
  · intro e; subst e
    rw [Finset.insert_eq_of_mem (by simp)] at h
    have := Finset.card_le_two (a := j) (b := i); omega
  · intro e; subst e
    rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self j)] at h
    have := Finset.card_le_two (a := i) (b := j); omega

theorem set_iff (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (i j k : Fin n) :
    ({i, j, k} : Finset (Fin n)) = {a, b, c} ↔
      (i, j, k) ∈ ({(a, b, c), (a, c, b), (b, a, c), (b, c, a), (c, a, b), (c, b, a)} :
        Finset (Fin n × Fin n × Fin n)) := by
  have hS : ({a, b, c} : Finset (Fin n)).card = 3 := Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  constructor
  · intro h
    have hd := distinct_of_card i j k (h ▸ hS)
    have hi : i ∈ ({a, b, c} : Finset (Fin n)) := by rw [← h]; simp
    have hj : j ∈ ({a, b, c} : Finset (Fin n)) := by rw [← h]; simp
    have hk : k ∈ ({a, b, c} : Finset (Fin n)) := by rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk ⊢
    obtain ⟨d1, d2, d3⟩ := hd
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl <;> simp_all
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
    have hsub : ({i, j, k} : Finset (Fin n)) ⊆ {a, b, c} := by
      rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> intro x hx <;> simp only [Finset.mem_insert,
          Finset.mem_singleton] at hx ⊢ <;> tauto
    have hcard : ({i, j, k} : Finset (Fin n)).card = 3 := by
      apply Finset.card_eq_three.mpr
      refine ⟨i, j, k, ?_, ?_, ?_, rfl⟩ <;>
      rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
        first | exact hab | exact hac | exact hbc | exact hab.symm | exact hac.symm | exact hbc.symm
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hS, hcard])

theorem P_eq (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (u v w : Vec n) :
    (∑ i, ∑ j, ∑ k, if ({i, j, k} : Finset (Fin n)) = {a, b, c} then u i * v j * w k else 0) =
      u a * v b * w c + u a * v c * w b + u b * v a * w c + u b * v c * w a +
        u c * v a * w b + u c * v b * w a := by
  have h1 : (∑ i, ∑ j, ∑ k, if ({i, j, k} : Finset (Fin n)) = {a, b, c} then u i * v j * w k else 0) =
      ∑ p : Fin n × Fin n × Fin n, if p ∈ ({(a, b, c), (a, c, b), (b, a, c), (b, c, a), (c, a, b),
        (c, b, a)} : Finset (Fin n × Fin n × Fin n)) then u p.1 * v p.2.1 * w p.2.2 else 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro i _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    simp only [set_iff a b c hab hac hbc]
  rw [h1, Finset.sum_ite_mem, Finset.univ_inter]
  rw [Finset.sum_insert (by simp [hbc, hab, hac, Ne.symm hab, Ne.symm hac, Ne.symm hbc]),
    Finset.sum_insert (by simp [hbc, hab, hac, Ne.symm hab, Ne.symm hac, Ne.symm hbc]),
    Finset.sum_insert (by simp [hbc, hab, hac, Ne.symm hab, Ne.symm hac, Ne.symm hbc]),
    Finset.sum_insert (by simp [hbc, hab, hac, Ne.symm hab, Ne.symm hac, Ne.symm hbc]),
    Finset.sum_insert (by simp [hbc, hab, hac, Ne.symm hab, Ne.symm hac, Ne.symm hbc]),
    Finset.sum_singleton]
  ring

theorem coeff3_eq (f : CubicPoly n) (i j k : Fin n) :
    f.coeff3 i j k = ∑ S : Mono n 3, if ({i, j, k} : Finset (Fin n)) = S.1 then f.c3 S else 0 := by
  unfold CubicPoly.coeff3
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨{i, j, k}, h⟩]
    · simp
    · intro S _ hS
      rw [if_neg]
      intro e; exact hS (Subtype.ext e.symm)
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · symm
    apply Finset.sum_eq_zero
    intro S _
    rw [if_neg]
    intro e; exact h (e ▸ S.2)

end Aux_PIQ16

open PlantedIQP Aux_PIQ16 in
theorem solution {n : ℕ} (f : CubicPoly n) (u v w : Vec n) :
    triForm f u v w = f.eval (u + v + w) + f.eval (u + v) + f.eval (v + w) + f.eval (u + w) +
      f.eval u + f.eval v + f.eval w := by
  set Q : Mono n 3 → ZMod 2 := fun S =>
    ∑ i, ∑ j, ∑ k, (if ({i, j, k} : Finset (Fin n)) = S.1 then u i * v j * w k else 0) with hQ
  have hL : triForm f u v w = ∑ S : Mono n 3, f.c3 S * Q S := by
    unfold triForm
    calc ∑ i, ∑ j, ∑ k, u i * v j * w k * f.coeff3 i j k
        = ∑ i, ∑ j, ∑ k, ∑ S : Mono n 3, f.c3 S *
            (if ({i, j, k} : Finset (Fin n)) = S.1 then u i * v j * w k else 0) := by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          apply Finset.sum_congr rfl; intro k _
          rw [coeff3_eq, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro S _
          split_ifs <;> ring
      _ = ∑ i, ∑ j, ∑ S : Mono n 3, ∑ k, f.c3 S *
            (if ({i, j, k} : Finset (Fin n)) = S.1 then u i * v j * w k else 0) := by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          exact Finset.sum_comm
      _ = ∑ i, ∑ S : Mono n 3, ∑ j, ∑ k, f.c3 S *
            (if ({i, j, k} : Finset (Fin n)) = S.1 then u i * v j * w k else 0) := by
          apply Finset.sum_congr rfl; intro i _
          exact Finset.sum_comm
      _ = ∑ S : Mono n 3, ∑ i, ∑ j, ∑ k, f.c3 S *
            (if ({i, j, k} : Finset (Fin n)) = S.1 then u i * v j * w k else 0) := Finset.sum_comm
      _ = ∑ S : Mono n 3, f.c3 S * Q S := by
          apply Finset.sum_congr rfl; intro S _
          simp only [hQ, Finset.mul_sum]
  have hR : f.eval (u + v + w) + f.eval (u + v) + f.eval (v + w) + f.eval (u + w) +
      f.eval u + f.eval v + f.eval w =
      ∑ S : Mono n 3, f.c3 S * (∏ i ∈ S.1, (u + v + w) i + ∏ i ∈ S.1, (u + v) i +
        ∏ i ∈ S.1, (v + w) i + ∏ i ∈ S.1, (u + w) i + ∏ i ∈ S.1, u i + ∏ i ∈ S.1, v i +
        ∏ i ∈ S.1, w i) +
      ∑ S : Mono n 2, f.c2 S * (∏ i ∈ S.1, (u + v + w) i + ∏ i ∈ S.1, (u + v) i +
        ∏ i ∈ S.1, (v + w) i + ∏ i ∈ S.1, (u + w) i + ∏ i ∈ S.1, u i + ∏ i ∈ S.1, v i +
        ∏ i ∈ S.1, w i) +
      ∑ i, f.c1 i * ((u + v + w) i + (u + v) i + (v + w) i + (u + w) i + u i + v i + w i) := by
    unfold CubicPoly.eval
    simp only [mul_add, Finset.sum_add_distrib]
    ring
  have hA : ∀ S : Mono n 3, (∏ i ∈ S.1, (u + v + w) i + ∏ i ∈ S.1, (u + v) i +
        ∏ i ∈ S.1, (v + w) i + ∏ i ∈ S.1, (u + w) i + ∏ i ∈ S.1, u i + ∏ i ∈ S.1, v i +
        ∏ i ∈ S.1, w i) = Q S := by
    intro S
    obtain ⟨a, b, c, hab, hac, hbc, hS⟩ := Finset.card_eq_three.mp S.2
    simp only [hQ]
    rw [hS, P_eq a b c hab hac hbc]
    have ha : a ∉ ({b, c} : Finset (Fin n)) := by simp [hab, hac]
    simp only [Finset.prod_insert ha, Finset.prod_pair hbc, Pi.add_apply]
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc,
      ← mul_assoc]
    exact id3 _ _ _ _ _ _ _ _ _
  have hB : ∀ S : Mono n 2, (∏ i ∈ S.1, (u + v + w) i + ∏ i ∈ S.1, (u + v) i +
        ∏ i ∈ S.1, (v + w) i + ∏ i ∈ S.1, (u + w) i + ∏ i ∈ S.1, u i + ∏ i ∈ S.1, v i +
        ∏ i ∈ S.1, w i) = 0 := by
    intro S
    obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.mp S.2
    rw [hS]
    simp only [Finset.prod_pair hab, Pi.add_apply]
    exact id2 _ _ _ _ _ _
  have hC : ∀ i, ((u + v + w) i + (u + v) i + (v + w) i + (u + w) i + u i + v i + w i) = 0 := by
    intro i
    simp only [Pi.add_apply]
    exact id1 _ _ _
  rw [hR, hL]
  simp only [hA, hB, hC, mul_zero, Finset.sum_const_zero, add_zero]
