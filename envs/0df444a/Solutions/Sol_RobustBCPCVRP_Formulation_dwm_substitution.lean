-- Prove2me | solution 1 for RobustBCPCVRP.Formulation.dwm_substitution
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:22:36.477057+00:00
-- url     : https://prove2.me/submissions/6f2ed053-7ef9-411a-9cf4-bdfa40e8ebad

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_cut
import Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound
import Definitions.Def_RobustBCPCVRP_Formulation_Setting
import Definitions.Def_RobustBCPCVRP_Formulation_Polytopes
set_option autoImplicit false
open LysgaardCVRP.Shrink RobustBCPCVRP.Formulation

theorem ll_cut_colSum {n : ℕ} (lam : List (Fin (n + 1)) →₀ ℝ) (S : Finset (Fin (n + 1))) :
    cut (colSum lam) S = ∑ r ∈ lam.support, cutCoeff r S * lam r := by
  have e1 : cut (colSum lam) S = ∑ i ∈ S, ∑ j ∈ Sᶜ, ∑ r ∈ lam.support, lam r * (inc r s(i, j) : ℝ) := rfl
  have e2 : ∑ i ∈ S, ∑ j ∈ Sᶜ, ∑ r ∈ lam.support, lam r * (inc r s(i, j) : ℝ)
      = ∑ i ∈ S, ∑ r ∈ lam.support, ∑ j ∈ Sᶜ, lam r * (inc r s(i, j) : ℝ) :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
  have e3 : ∑ i ∈ S, ∑ r ∈ lam.support, ∑ j ∈ Sᶜ, lam r * (inc r s(i, j) : ℝ)
      = ∑ r ∈ lam.support, ∑ i ∈ S, ∑ j ∈ Sᶜ, lam r * (inc r s(i, j) : ℝ) := Finset.sum_comm
  rw [e1, e2, e3]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  unfold cutCoeff cut
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem solution {n : ℕ} (E : Finset (Sym2 (Fin (n + 1))))
    (d : Fin (n + 1) → ℕ) (K C : ℕ) (ℓ : Sym2 (Fin (n + 1)) → ℝ)
    (lam : List (Fin (n + 1)) →₀ ℝ) (hlam : IsColumns E d C lam) :
    (IsDWMFeasible E d K C lam ↔
      Deg1 (colSum lam) ∧ Deg2 K (colSum lam) ∧ Cap3 d C (colSum lam) ∧ Bnd4 E (colSum lam)) ∧
    OnE E (colSum lam) ∧ Nonneg (colSum lam) ∧
    dwmObjective E ℓ lam = ∑ e ∈ E, ℓ e * colSum lam e := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold IsDWMFeasible Deg1 Deg2 Cap3 Bnd4
    simp only [ll_cut_colSum]
    constructor
    · rintro ⟨-, h1, h2, h3, h4⟩
      refine ⟨h1, h2, h3, fun e he he0 => ?_⟩
      have := h4 e he he0
      unfold colSum
      calc ∑ r ∈ lam.support, lam r * (inc r e : ℝ) = ∑ r ∈ lam.support, (inc r e : ℝ) * lam r :=
            Finset.sum_congr rfl (fun r _ => mul_comm _ _)
        _ ≤ 1 := this
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨hlam, h1, h2, h3, fun e he he0 => ?_⟩
      have := h4 e he he0
      unfold colSum at this
      calc ∑ r ∈ lam.support, (inc r e : ℝ) * lam r = ∑ r ∈ lam.support, lam r * (inc r e : ℝ) :=
            Finset.sum_congr rfl (fun r _ => mul_comm _ _)
        _ ≤ 1 := this
  · intro e he
    unfold colSum
    refine Finset.sum_eq_zero (fun r hr => ?_)
    have hw := (hlam r hr).1.1
    have : e ∉ edges r := fun h => he (hw.2.2 e h)
    have : inc r e = 0 := List.count_eq_zero_of_not_mem this
    simp [this]
  · intro e
    unfold colSum
    exact Finset.sum_nonneg (fun r hr => mul_nonneg (hlam r hr).2 (Nat.cast_nonneg _))
  · unfold dwmObjective colSum
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    refine Finset.sum_congr rfl (fun e _ => ?_)
    ring
