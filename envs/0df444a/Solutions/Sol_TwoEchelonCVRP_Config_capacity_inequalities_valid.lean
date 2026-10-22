-- Prove2me | solution 1 for TwoEchelonCVRP.Config.capacity_inequalities_valid
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:43:59.236179+00:00
-- url     : https://prove2.me/submissions/447540ac-9207-4024-bae9-ce777286b6ab

import Mathlib
import Definitions.Def_TwoEchelonCVRP_Config_Configuration

set_option autoImplicit false

open TwoEchelonCVRP.Config

theorem solution (I : Instance) (RS : RouteSystem I) (M : Finset RS.FR)
    (t : SolFM RS) (ht : IsFeasibleFM RS M t) (H : Finset (Fin I.nc)) (hH : 2 ≤ H.card) :
    ⌈((∑ i ∈ H, I.q i : ℕ) : ℚ) / (I.Q2 : ℚ)⌉₊
      ≤ ∑ l ∈ Finset.univ.filter (fun l => RS.sat l ∈ NS RS M ∧ (RS.Rcust l ∩ H).Nonempty),
          (t.x l).toNat := by
  obtain ⟨_, hcover, _⟩ := ht
  have hQ : (0 : ℚ) < I.Q2 := by exact_mod_cast I.Q2_pos
  rw [Nat.ceil_le, div_le_iff₀ hQ]
  have per : ∀ l : RS.SR,
      (∑ i ∈ H, if (RS.sat l ∈ NS RS M ∧ i ∈ RS.tour2 l) then I.q i * (t.x l).toNat else 0) ≤
        if (RS.sat l ∈ NS RS M ∧ (RS.Rcust l ∩ H).Nonempty) then (t.x l).toNat * I.Q2 else 0 := by
    intro l
    by_cases hs : RS.sat l ∈ NS RS M
    · by_cases hne : (RS.Rcust l ∩ H).Nonempty
      · simp only [hs, true_and, hne, if_true]
        rw [← Finset.sum_filter, ← Finset.sum_mul]
        have h1 : ∑ i ∈ H.filter (fun i => i ∈ RS.tour2 l), I.q i ≤ I.Q2 := by
          refine le_trans (Finset.sum_le_sum_of_subset ?_) (RS.cap2 l)
          intro i hi
          have := (Finset.mem_filter.1 hi).2
          simpa using this
        calc _ ≤ I.Q2 * (t.x l).toNat := Nat.mul_le_mul_right _ h1
          _ = _ := mul_comm _ _
      · simp only [hs, true_and, hne, if_false]
        apply le_of_eq
        apply Finset.sum_eq_zero
        intro i hi
        rw [if_neg]
        intro hmem
        exact hne ⟨i, Finset.mem_inter.2 ⟨by simpa [RouteSystem.Rcust] using hmem, hi⟩⟩
    · simp [hs]
  have nat_ineq : ∑ i ∈ H, I.q i ≤
      (∑ l ∈ Finset.univ.filter (fun l => RS.sat l ∈ NS RS M ∧ (RS.Rcust l ∩ H).Nonempty),
          (t.x l).toNat) * I.Q2 := by
    calc ∑ i ∈ H, I.q i
        = ∑ i ∈ H, I.q i * ∑ l ∈ Finset.univ.filter
            (fun l => RS.sat l ∈ NS RS M ∧ i ∈ RS.tour2 l), (t.x l).toNat := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hcover i, mul_one]
      _ = ∑ i ∈ H, ∑ l : RS.SR,
            if (RS.sat l ∈ NS RS M ∧ i ∈ RS.tour2 l) then I.q i * (t.x l).toNat else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum, Finset.sum_filter]
      _ = ∑ l : RS.SR, ∑ i ∈ H,
            if (RS.sat l ∈ NS RS M ∧ i ∈ RS.tour2 l) then I.q i * (t.x l).toNat else 0 :=
          Finset.sum_comm
      _ ≤ ∑ l : RS.SR,
            if (RS.sat l ∈ NS RS M ∧ (RS.Rcust l ∩ H).Nonempty) then (t.x l).toNat * I.Q2 else 0 :=
          Finset.sum_le_sum (fun l _ => per l)
      _ = (∑ l ∈ Finset.univ.filter (fun l => RS.sat l ∈ NS RS M ∧ (RS.Rcust l ∩ H).Nonempty),
          (t.x l).toNat) * I.Q2 := by
          rw [Finset.sum_mul, Finset.sum_filter]
  exact_mod_cast nat_ineq
