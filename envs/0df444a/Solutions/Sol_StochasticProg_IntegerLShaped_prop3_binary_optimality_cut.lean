-- Prove2me | solution 1 for StochasticProg.IntegerLShaped.prop3_binary_optimality_cut
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:04:45.25615+00:00
-- url     : https://prove2.me/submissions/0048d901-7857-4a31-8088-2818fd40b196

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_IntegerLShaped_Instance

namespace StochasticProg.IntegerLShaped

open StochasticProg.Recourse

theorem aux_p3b_delta_le {n1 : ℕ} (S : Finset (Fin n1)) (x : Fin n1 → ℝ) (hx : Binary x)
    (hne : x ≠ indicator S) : delta S x ≤ (S.card : ℝ) - 1 := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ indicator S i := Function.ne_iff.mp hne
  set f : Fin n1 → ℝ := fun j => if j ∈ S then 1 - x j else x j with hf
  have hsum : ∑ j, f j = (S.card : ℝ) - delta S x := by
    rw [← Finset.sum_add_sum_compl S f]
    simp only [delta, hf]
    rw [Finset.sum_congr rfl (fun j hj => if_pos hj),
      Finset.sum_congr rfl (fun j hj => if_neg (Finset.mem_compl.mp hj))]
    rw [Finset.sum_sub_distrib]
    simp
    ring
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ f j := by
    intro j _
    simp only [hf]
    rcases hx j with h | h <;> split_ifs <;> simp [h]
  have hfi : 1 ≤ f i := by
    simp only [hf]
    simp only [indicator] at hi
    rcases hx i with h | h <;> split_ifs at hi ⊢ <;> simp_all
  have := Finset.single_le_sum hnn (Finset.mem_univ i)
  linarith

theorem aux_p3b_delta_ind {n1 : ℕ} (S : Finset (Fin n1)) :
    delta S (indicator S) = (S.card : ℝ) := by
  unfold delta indicator
  rw [Finset.sum_congr rfl (fun j hj => if_pos hj),
    Finset.sum_congr rfl (fun j hj => if_neg (Finset.mem_compl.mp hj))]
  simp

theorem aux_p3b_ind_bin {n1 : ℕ} (S : Finset (Fin n1)) : Binary (indicator S) := by
  intro i
  unfold indicator
  split_ifs <;> simp

end StochasticProg.IntegerLShaped

open StochasticProg.IntegerLShaped
open StochasticProg.Recourse

theorem solution {n1 n2 m1 m2 K : ℕ} (d : Data n1 n2 m1 m2 K) (L : ℝ)
    (hL : ∀ x', x' ∈ K1X d → Binary x' → (L : EReal) ≤ QY d x')
    (S : Finset (Fin n1)) (hSfeas : indicator S ∈ K1X d) (qS : ℝ)
    (hqS : (qS : EReal) = QY d (indicator S))
    (x' : Fin n1 → ℝ) (hx' : x' ∈ K1X d) (hx'bin : Binary x') :
    (cutRHS L qS S x' : EReal) ≤ QY d x' := by
  have hLq : L ≤ qS := by
    have h := hL _ hSfeas (aux_p3b_ind_bin S)
    rw [← hqS] at h
    exact_mod_cast h
  by_cases hx : x' = indicator S
  · subst hx
    have : cutRHS L qS S (indicator S) = qS := by
      unfold cutRHS
      rw [aux_p3b_delta_ind]
      ring
    rw [this, hqS]
  · have hd := aux_p3b_delta_le S x' hx'bin hx
    have : cutRHS L qS S x' ≤ L := by
      unfold cutRHS
      nlinarith [mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr hLq)]
    calc (cutRHS L qS S x' : EReal) ≤ (L : EReal) := by exact_mod_cast this
      _ ≤ QY d x' := hL x' hx' hx'bin
