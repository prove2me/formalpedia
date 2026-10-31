-- Prove2me | solution 1 for VdNSim.Sparse.eqs_6_8
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T21:21:50.461918+00:00
-- url     : https://prove2.me/submissions/d46842a7-79de-421d-98ed-b9b5d829d4d6

import Mathlib
import Definitions.Def_VdNSim_Sparse_Model

noncomputable section

namespace Aux_VdN_eqs_6_8
open VdNSim.Sparse

lemma cancel_prob_div (u v : ℂ) (p : ℂ) (hp : p ≠ 0) :
    p * (u / p * v) = v * u := by
  calc p * (u / p * v)
    _ = (p * (u / p)) * v := by rw [mul_assoc]
    _ = (u / p * p) * v := by rw [mul_comm p]
    _ = u * v := by rw [div_mul_cancel₀ u hp]
    _ = v * u := by rw [mul_comm]

lemma prob_zero_imp_psi_zero {X : Type*} (ψ : X → ℂ) (x : X) (h : prob ψ x = 0) :
    ψ x = 0 := by
  unfold prob at h
  have : ‖ψ x‖ = 0 := sq_eq_zero_iff.mp h
  exact norm_eq_zero.mp this

lemma prob_mul_F {X : Type*} [Fintype X] [DecidableEq X]
    {A : Matrix X X ℂ} {s : ℕ} (D : ColumnData A s) (ψ ϕ : X → ℂ) (i : Fin s) (x : X) :
    (prob ψ x : ℂ) * F ψ ϕ D i x =
      if prob ϕ (D.r i x) ≤ prob ψ x then D.α i x * star (ϕ (D.r i x)) * ψ x else 0 := by
  unfold F
  split_ifs with hle
  · by_cases hp : prob ψ x = 0
    · have hψ : ψ x = 0 := prob_zero_imp_psi_zero ψ x hp
      rw [hψ]
      simp
    · have hpC : (prob ψ x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp
      have hcan := cancel_prob_div (star (ϕ (D.r i x)) * ψ x) (D.α i x) (prob ψ x : ℂ) hpC
      rw [hcan, mul_assoc]
  · rw [mul_zero]

lemma prob_mul_G {X : Type*} [Fintype X] [DecidableEq X]
    {A : Matrix X X ℂ} {s : ℕ} (D : ColumnData A s) (ψ ϕ : X → ℂ) (i : Fin s) :
    expect (prob ϕ) (G ψ ϕ D i) =
      ∑ x, if prob ψ x < prob ϕ (D.r i x) then D.α i x * star (ϕ (D.r i x)) * ψ x else 0 := by
  unfold expect G
  simp_rw [Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_eq_single (D.r i x)]
  · by_cases hα : D.α i x = 0
    · have hfalse : ¬ (D.r i x = D.r i x ∧ D.α i x ≠ 0) := fun h => h.2 hα
      rw [if_neg hfalse]
      split_ifs <;> simp [hα]
    · have htrue : D.r i x = D.r i x ∧ D.α i x ≠ 0 := ⟨rfl, hα⟩
      rw [if_pos htrue]
      split_ifs with hlt
      · have h0 : 0 ≤ prob ψ x := by
          unfold prob
          positivity
        have hpos : 0 < prob ϕ (D.r i x) := lt_of_le_of_lt h0 hlt
        have hpC : (prob ϕ (D.r i x) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
        have hcan := cancel_prob_div (star (ϕ (D.r i x)) * ψ x) (D.α i x) (prob ϕ (D.r i x) : ℂ) hpC
        rw [hcan, mul_assoc]
      · rw [mul_zero]
  · intro b _ hb
    have hne : ¬ (D.r i x = b ∧ D.α i x ≠ 0) := by
      intro h
      exact hb (h.1.symm)
    rw [if_neg hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Aux_VdN_eqs_6_8

open VdNSim.Sparse Aux_VdN_eqs_6_8 in
theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    {A : Matrix X X ℂ} {s : ℕ} (D : ColumnData A s) (ψ ϕ : X → ℂ)
    (i : Fin s) :
    (∑ x, D.α i x * star (ϕ (D.r i x)) * ψ x) =
      expect (prob ψ) (F ψ ϕ D i) + expect (prob ϕ) (G ψ ϕ D i) := by
  have hF : expect (prob ψ) (F ψ ϕ D i) =
      ∑ x, if prob ϕ (D.r i x) ≤ prob ψ x then D.α i x * star (ϕ (D.r i x)) * ψ x else 0 := by
    unfold expect
    refine Finset.sum_congr rfl (fun x _ => prob_mul_F D ψ ϕ i x)
  rw [hF, prob_mul_G D ψ ϕ i, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hle : prob ϕ (D.r i x) ≤ prob ψ x
  · have hlt : ¬ (prob ψ x < prob ϕ (D.r i x)) := not_lt.mpr hle
    rw [if_pos hle, if_neg hlt, add_zero]
  · have hlt : prob ψ x < prob ϕ (D.r i x) := not_le.mp hle
    rw [if_neg hle, if_pos hlt, zero_add]
