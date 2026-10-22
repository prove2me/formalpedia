-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P33.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:28:53.254305+00:00
-- url     : https://prove2.me/submissions/603c318e-1598-4e30-a1f8-5dc1ddf7cf0c

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

lemma g67h_all3 {n : ℕ} (x y z : Finset (Fin n)) : allParties ![x, y, z] = x ∪ y ∪ z := by
  ext t; simp [allParties, Fin.exists_fin_succ]

lemma g67h_all2 {n : ℕ} (x y : Finset (Fin n)) : allParties ![x, y] = x ∪ y := by
  ext t; simp [allParties, Fin.exists_fin_succ]

lemma g67h_er3 {n : ℕ} (x y z : Finset (Fin n)) :
    ((Finset.univ.erase (0 : Fin 3)).biUnion ![x, y, z] = y ∪ z) ∧
    ((Finset.univ.erase (1 : Fin 3)).biUnion ![x, y, z] = x ∪ z) ∧
    ((Finset.univ.erase (2 : Fin 3)).biUnion ![x, y, z] = x ∪ y) := by
  refine ⟨?_, ?_, ?_⟩ <;> ext t <;> simp [Fin.exists_fin_succ] <;> tauto

theorem solution {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (hrho : IsDensityMatrix rho) (a ap b bp c cp e : Finset (Fin n))
    (hdis : DisjointRegisters ![a,ap,b,bp,c,cp] e) :
    (info .total rho ![a ∪ ap,b ∪ bp,c ∪ cp] e =
      info .total rho ![a,b,c] (ap ∪ bp ∪ cp ∪ e) +
      info .total rho ![ap,bp,cp] e +
      info .total rho ![a,bp ∪ cp] (ap ∪ e) +
      info .total rho ![b,ap ∪ cp] (bp ∪ e) +
      info .total rho ![c,ap ∪ bp] (cp ∪ e)) ∧
    (info .dual rho ![a ∪ ap,b ∪ bp,c ∪ cp] e =
      info .dual rho ![a,b,c] (ap ∪ bp ∪ cp ∪ e) +
      info .dual rho ![ap,bp,cp] e +
      info .total rho ![a ∪ b,cp] (ap ∪ bp ∪ e) +
      info .total rho ![a ∪ c,bp] (ap ∪ cp ∪ e) +
      info .total rho ![b ∪ c,ap] (bp ∪ cp ∪ e)) := by
  have hE : ∀ x y z : Finset (Fin n), (Finset.univ.erase (0 : Fin 3)).biUnion ![x, y, z] = y ∪ z :=
    fun x y z => (g67h_er3 x y z).1
  have hE1 : ∀ x y z : Finset (Fin n), (Finset.univ.erase (1 : Fin 3)).biUnion ![x, y, z] = x ∪ z :=
    fun x y z => (g67h_er3 x y z).2.1
  have hE2 : ∀ x y z : Finset (Fin n), (Finset.univ.erase (2 : Fin 3)).biUnion ![x, y, z] = x ∪ y :=
    fun x y z => (g67h_er3 x y z).2.2
  constructor
  · simp only [info, conditionalMultipartiteInformation, Fin.sum_univ_three, Fin.sum_univ_two,
      g67h_all3, g67h_all2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    simp only [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm, Finset.union_self,
      Finset.union_left_idem]
    push_cast
    ring
  · simp only [info, conditionalMultipartiteInformation, Fin.sum_univ_three, Fin.sum_univ_two,
      g67h_all3, g67h_all2, hE, hE1, hE2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    simp only [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm, Finset.union_self,
      Finset.union_left_idem]
    push_cast
    ring
