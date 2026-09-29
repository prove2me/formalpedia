-- Prove2me | solution 1 for SX.six_exponentials_of_numberField
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T11:15:29.196718+00:00
-- url     : https://prove2.me/submissions/e54a15db-1498-4685-945a-a58efa0239bb

import Theorems.Thm_SX_exists_aux_expSum
import Theorems.Thm_SX_descent_step
import Theorems.Thm_SX_eq_zero_of_expSum_vanishes

/-! # Assembly check: rung 2 from rungs 3, 4, 5.  Must contain no `sorry`. -/

open Complex

theorem solution
    {d l : ℕ} (hdl : d + l < d * l)
    (x : Fin d → ℂ) (y : Fin l → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] :
    ∃ i j, Complex.exp (x i * y j) ∉ K := by
  classical
  have hl2 : 2 ≤ l := by
    by_contra hcl
    push_neg at hcl
    interval_cases l <;> omega
  by_contra hcon
  push_neg at hcon
  obtain ⟨c, hc, M₁, haux⟩ := SX.exists_aux_expSum hdl x y hx hy K hcon
  obtain ⟨M₀, hdesc⟩ := SX.descent_step hdl x y hx hy K hcon c hc
  set M : ℕ := max M₀ M₁ + 1 with hMdef
  obtain ⟨L, hL0, hLc, p, ⟨lam0, hlam0mem, hlam0⟩, hph, hvan⟩ :=
    haux M (by omega)
  have key : ∀ N : ℕ, M ≤ N →
      ∀ m : Fin l → ℕ, (∀ j, m j < N) → SX.expSum x L p (SX.latticeSum y m) = 0 := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => exact hvan
    | succ N hN ih => exact hdesc M (by omega) L hL0 hLc p hph N hN ih
  have hall : ∀ m : Fin l → ℕ, SX.expSum x L p (SX.latticeSum y m) = 0 := by
    intro m
    refine key (max M (Finset.univ.sup m + 1)) (le_max_left _ _) m fun j => ?_
    exact lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ j)))
      (le_max_right _ _)
  exact hlam0 (SX.eq_zero_of_expSum_vanishes hl2 x y hx hy L p hall lam0 hlam0mem)

