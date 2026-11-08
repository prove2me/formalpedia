-- Prove2me | solution 1 for PairwiseRealize.walsh_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:12:49.323209+00:00
-- url     : https://prove2.me/submissions/50f671a1-a47f-49c2-ab48-5b58e015db54

import Mathlib
import Definitions.Def_PairwiseRealize_Model

namespace Aux_PRwalsh

open PairwiseRealize

def S {n : ℕ} : Feat n → Finset (Fin n)
  | Sum.inl _ => ∅
  | Sum.inr (Sum.inl i) => {i}
  | Sum.inr (Sum.inr p) => {p.1.1, p.1.2}

theorem vR_eq {n : ℕ} (x : Row n) (f : Feat n) :
    vR n x f = ∏ k, (if k ∈ S f then (sgn (x k) : ℝ) else 1) := by
  rw [Finset.prod_ite_mem, Finset.univ_inter]
  rcases f with u | i | p
  · simp [vR, vvec, S]
  · simp [vR, vvec, S]
  · have hne : p.1.1 ≠ p.1.2 := ne_of_lt p.2
    simp only [vR, vvec, S]
    rw [Finset.prod_pair hne]
    push_cast
    ring

theorem S_inj {n : ℕ} (f g : Feat n) (h : S f = S g) : f = g := by
  rcases f with u | i | p <;> rcases g with u' | i' | p'
  · rfl
  · simp [S] at h
  · exact absurd h.symm (Finset.insert_ne_empty _ _)
  · simp [S] at h
  · simp only [S, Finset.singleton_inj] at h; rw [h]
  · exfalso
    simp only [S] at h
    have h1 := congrArg Finset.card h
    rw [Finset.card_singleton, Finset.card_pair (ne_of_lt p'.2)] at h1
    omega
  · exact absurd h (Finset.insert_ne_empty _ _)
  · exfalso
    simp only [S] at h
    have h1 := congrArg Finset.card h
    rw [Finset.card_singleton, Finset.card_pair (ne_of_lt p.2)] at h1
    omega
  · simp only [S] at h
    obtain ⟨⟨a, b⟩, hab⟩ := p
    obtain ⟨⟨c, d⟩, hcd⟩ := p'
    simp only at h hab hcd
    have ha : a ∈ ({c, d} : Finset (Fin n)) := by rw [← h]; simp
    have hb : b ∈ ({c, d} : Finset (Fin n)) := by rw [← h]; simp
    have hc : c ∈ ({a, b} : Finset (Fin n)) := by rw [h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
    have hab' : a.val < b.val := hab
    have hcd' : c.val < d.val := hcd
    have ha' : a.val = c.val ∨ a.val = d.val := by rcases ha with h | h <;> simp [h]
    have hb' : b.val = c.val ∨ b.val = d.val := by rcases hb with h | h <;> simp [h]
    have e1 : a = c := Fin.ext (by omega)
    have e2 : b = d := Fin.ext (by omega)
    subst e1 e2
    rfl

theorem bool_sum (P Q : Prop) [Decidable P] [Decidable Q] :
    (∑ b : Bool, (if P then (sgn b : ℝ) else 1) * (if Q then (sgn b : ℝ) else 1)) =
      if (P ↔ Q) then 2 else 0 := by
  rw [Fintype.sum_bool]
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ, sgn, bv] <;> norm_num

end Aux_PRwalsh

open PairwiseRealize Aux_PRwalsh in
theorem solution (n : ℕ) :
    ∑ x : Row n, Matrix.vecMulVec (vR n x) (vR n x) =
      (2 ^ n : ℝ) • (1 : Matrix (Feat n) (Feat n) ℝ) := by
  ext f g
  rw [Matrix.sum_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  simp only [Matrix.vecMulVec_apply, vR_eq, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun k b => (if k ∈ S f then (sgn b : ℝ) else 1) *
    (if k ∈ S g then (sgn b : ℝ) else 1))]
  simp only [bool_sum]
  by_cases hfg : f = g
  · subst hfg
    simp
  · rw [if_neg hfg, mul_zero]
    have : S f ≠ S g := fun h => hfg (S_inj f g h)
    obtain ⟨k, hk⟩ : ∃ k, ¬ (k ∈ S f ↔ k ∈ S g) := by
      by_contra hc
      push_neg at hc
      exact this (Finset.ext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by rw [if_neg hk])
