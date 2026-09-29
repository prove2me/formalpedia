-- Prove2me | solution 1 for Set.ncard_pairing_annihilator_mul_ncard_eq_ncard_mul_ncard_radical
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/0025ebac-c4f6-512c-96a9-dd4a3b4af19b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Set_ncard_pairing_annihilator_mul_ncard_eq_ncard_mul_ncard_radical

set_option autoImplicit false

namespace AnnCount2

variable {J : Type} {L : Type} [Field L]

theorem sum_eq_zero_of_translate [AddCommGroup J] (s : Finset J) (g : J) (hs : ∀ x ∈ s, g + x ∈ s) (hs' : ∀ x ∈ s, -g + x ∈ s)
    (f : J → L) (c : L) (hc : c ≠ 1) (hf : ∀ x ∈ s, f (g + x) = c * f x) :
    ∑ x ∈ s, f x = 0 := by
  have hre : ∑ x ∈ s, f (g + x) = ∑ x ∈ s, f x := by
    apply Finset.sum_nbij' (fun x => g + x) (fun x => -g + x)
    · intro x hx; exact hs x hx
    · intro x hx; exact hs' x hx
    · intro x hx; simp
    · intro x hx; simp
    · intro x hx; rfl
  have h2 : ∑ x ∈ s, f (g + x) = c * ∑ x ∈ s, f x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x hx => hf x hx)
  have h3 : (c - 1) * ∑ x ∈ s, f x = 0 := by rw [sub_mul, one_mul, ← h2, hre, sub_self]
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd (sub_eq_zero.1 h) hc
  · exact h

theorem sum_eq_card_of_forall_eq_one (s : Finset J) (f : J → L) (hf : ∀ x ∈ s, f x = 1) :
    ∑ x ∈ s, f x = s.card := by
  rw [Finset.sum_congr rfl hf, Finset.sum_const, nsmul_eq_mul, mul_one]

end AnnCount2

open AnnCount2 in

theorem solution
    {J J' : Type} [AddCommGroup J] [AddCommGroup J'] {L : Type} [Field L] [CharZero L]
    (A : Set J) (X' : Set J') (hA : A.Finite) (hX' : X'.Finite)
    (hA0 : (0 : J) ∈ A) (hAadd : ∀ x ∈ A, ∀ y ∈ A, x + y ∈ A) (hAneg : ∀ x ∈ A, -x ∈ A)
    (hX'0 : (0 : J') ∈ X') (hX'add : ∀ x ∈ X', ∀ y ∈ X', x + y ∈ X') (hX'neg : ∀ x ∈ X', -x ∈ X')
    (B : J → J' → L)
    (hBl : ∀ a ∈ A, ∀ a' ∈ A, ∀ y ∈ X', B (a + a') y = B a y * B a' y)
    (hBr : ∀ a ∈ A, ∀ y ∈ X', ∀ y' ∈ X', B a (y + y') = B a y * B a y') :
    Set.ncard {y : J' | y ∈ X' ∧ ∀ a ∈ A, B a y = 1} * Set.ncard A =
      Set.ncard X' * Set.ncard {a : J | a ∈ A ∧ ∀ y ∈ X', B a y = 1} := by
  classical
  set sX := hX'.toFinset with hsX
  set sA := hA.toFinset with hsA
  have memX : ∀ x, x ∈ sX ↔ x ∈ X' := fun x => Set.Finite.mem_toFinset hX'
  have memA : ∀ a, a ∈ sA ↔ a ∈ A := fun a => Set.Finite.mem_toFinset hA
  have hAnn : Set.ncard {y : J' | y ∈ X' ∧ ∀ a ∈ A, B a y = 1} = (sX.filter (fun y => ∀ a ∈ A, B a y = 1)).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, Finset.coe_filter, memX]
  have hKer : Set.ncard {a : J | a ∈ A ∧ ∀ y ∈ X', B a y = 1} = (sA.filter (fun a => ∀ y ∈ X', B a y = 1)).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext a
    simp only [Set.mem_setOf_eq, Finset.coe_filter, memA]
  have hXc : Set.ncard X' = sX.card := by rw [hsX, Set.ncard_eq_toFinset_card X' hX']
  have hAc : Set.ncard A = sA.card := by rw [hsA, Set.ncard_eq_toFinset_card A hA]
  have hrow : ∀ a ∈ sA, ∑ x ∈ sX, B a x = if (∀ y ∈ X', B a y = 1) then (sX.card : L) else 0 := by
    intro a ha
    have haA : a ∈ A := (memA a).1 ha
    split_ifs with h
    · exact sum_eq_card_of_forall_eq_one sX _ (fun x hx => h x ((memX x).1 hx))
    · push_neg at h
      obtain ⟨g, hg, hg1⟩ := h
      refine sum_eq_zero_of_translate sX g (fun x hx => (memX _).2 (hX'add g hg x ((memX x).1 hx)))
        (fun x hx => (memX _).2 (hX'add (-g) (hX'neg g hg) x ((memX x).1 hx))) (fun x => B a x) (B a g) hg1 ?_
      intro x hx
      exact hBr a haA g hg x ((memX x).1 hx)
  have hcol : ∀ x ∈ sX, ∑ a ∈ sA, B a x = if (∀ a ∈ A, B a x = 1) then (sA.card : L) else 0 := by
    intro x hx
    have hxX : x ∈ X' := (memX x).1 hx
    split_ifs with h
    · exact sum_eq_card_of_forall_eq_one sA _ (fun a ha => h a ((memA a).1 ha))
    · push_neg at h
      obtain ⟨g, hg, hg1⟩ := h
      refine sum_eq_zero_of_translate sA g (fun a ha => (memA _).2 (hAadd g hg a ((memA a).1 ha)))
        (fun a ha => (memA _).2 (hAadd (-g) (hAneg g hg) a ((memA a).1 ha))) (fun a => B a x) (B g x) hg1 ?_
      intro a ha
      exact hBl g hg a ((memA a).1 ha) x hxX
  have hsum : ∑ a ∈ sA, ∑ x ∈ sX, B a x = ∑ x ∈ sX, ∑ a ∈ sA, B a x := Finset.sum_comm
  rw [Finset.sum_congr rfl hrow, Finset.sum_congr rfl hcol, Finset.sum_ite, Finset.sum_ite, Finset.sum_const_zero,
    Finset.sum_const_zero, add_zero, add_zero, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul] at hsum
  rw [hAnn, hKer, hXc, hAc]
  have h'' : ((sX.filter (fun y => ∀ a ∈ A, B a y = 1)).card * sA.card : ℕ) =
      ((sA.filter (fun a => ∀ y ∈ X', B a y = 1)).card * sX.card : ℕ) := by
    exact_mod_cast hsum.symm
  rw [h'', mul_comm]

end S_Set_ncard_pairing_annihilator_mul_ncard_eq_ncard_mul_ncard_radical
end P2MW
export P2MW.S_Set_ncard_pairing_annihilator_mul_ncard_eq_ncard_mul_ncard_radical (solution)
