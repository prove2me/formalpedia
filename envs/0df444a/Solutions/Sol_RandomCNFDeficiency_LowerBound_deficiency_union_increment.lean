-- Prove2me | solution 1 for RandomCNFDeficiency.LowerBound.deficiency_union_increment
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-25T20:00:33.763166+00:00
-- url     : https://prove2.me/submissions/70299784-e3e8-41e9-a854-905efef6a7b1

import Definitions.Def_RandomCNFDeficiency_LowerBound_DeficiencyClosure
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
noncomputable section
open RandomCNFDeficiency.LowerBound
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BatchCNFPrivate
variable {n : ℕ}
lemma neighbor_union (A B : CNF n) : neighborhood (A ∪ B)=neighborhood A ∪ neighborhood B := by
  ext i
  simp only [neighborhood,Finset.mem_biUnion,Finset.mem_union]
  aesop


lemma gain (T : Finset (Fin n)) (A B : CNF n) :
    deficiency T (A ∪ B)-deficiency T A=
      ((B \ A).card : ℤ)-(((neighborhood B \ T) \ (neighborhood A \ T)).card : ℤ) := by
  have hC := Finset.card_sdiff_add_card B A
  rw [Finset.union_comm B A] at hC
  have hN := Finset.card_sdiff_add_card (neighborhood B \ T) (neighborhood A \ T)
  rw [Finset.union_comm (neighborhood B \ T) (neighborhood A \ T)] at hN
  have he : neighborhood (A ∪ B) \ T=(neighborhood A \ T) ∪ (neighborhood B \ T) := by
    rw [neighbor_union,Finset.union_sdiff_distrib]
  unfold deficiency
  rw [he]
  omega


theorem deficiency_union_increment (T : Finset (Fin n)) (A L : CNF n)
    (h : Disjoint A L) :
    deficiency T (A ∪ L) - deficiency T A =
      (L.card : ℤ) - ((neighborhood L \ (T ∪ neighborhood A)).card : ℤ) := by
  rw [gain]
  have hL : L \ A = L := Finset.sdiff_eq_self_iff_disjoint.mpr h.symm
  have hN : (neighborhood L \ T) \ (neighborhood A \ T) =
      neighborhood L \ (T ∪ neighborhood A) := by
    ext i
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  rw [hL,hN]


end BatchCNFPrivate
end
open RandomCNFDeficiency.LowerBound

set_option autoImplicit false

theorem solution {n : ℕ} (T : Finset (Fin n)) (A L : CNF n)
    (h : Disjoint A L) :
    deficiency T (A ∪ L) - deficiency T A =
      (L.card : ℤ) - ((neighborhood L \ (T ∪ neighborhood A)).card : ℤ) := by
  exact BatchCNFPrivate.deficiency_union_increment T A L h