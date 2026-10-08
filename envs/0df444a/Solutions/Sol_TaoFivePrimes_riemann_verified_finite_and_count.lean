-- Prove2me | solution 1 for TaoFivePrimes.riemann_verified_finite_and_count
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-10-05T12:39:54.749008+00:00
-- url     : https://prove2.me/submissions/55f2145e-4ef2-445d-94fb-4acca8370a19

import Mathlib
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_SeamClosed
import Theorems.Thm_TaoFivePrimes_riemann_verified_zero_set_finite
import Theorems.Thm_TaoFivePrimes_riemann_verified_zero_count_analytic

open Complex Set
open scoped BigOperators

theorem solution :
    {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧
      s.im ≤ 3.29 * 10 ^ 9}.Finite ∧
      {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧
        s.im ≤ 3.29 * 10 ^ 9}.ncard ≤ 10 ^ 10 := by
  set Z : Set ℂ := {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧
      s.im ≤ 3.29 * 10 ^ 9} with hZ
  set W : Set ℂ := {s : ℂ | riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧
      s.im ≤ 3.29 * 10 ^ 9} with hW
  have hZfin : Z.Finite := TaoFivePrimes.riemann_verified_zero_set_finite
  have hcount : (∑ᶠ s ∈ W, (analyticOrderNatAt riemannZeta s : ℝ)) ≤ (10 : ℝ) ^ 10 := by
    rw [hW]
    exact TaoFivePrimes.riemann_verified_zero_count_analytic
  have hZsubW : Z ⊆ W := by
    intro s hs
    exact ⟨hs.1, hs.2.1.le, hs.2.2.1.le, hs.2.2.2.1, hs.2.2.2.2⟩
  have hWfin : W.Finite := by
    have hK : IsCompact ((Set.Icc (0 : ℝ) 1) ×ℂ (Set.Icc (0 : ℝ) (3.29 * 10 ^ 9))) :=
      isCompact_Icc.reProdIm isCompact_Icc
    refine (hK.inter_riemannZetaZeros_finite).subset ?_
    intro s hs
    rw [hW] at hs
    obtain ⟨hz, hre0, hre1, him0, himT⟩ := hs
    exact ⟨⟨⟨hre0, hre1⟩, ⟨him0, himT⟩⟩, hz⟩
  constructor
  · exact hZfin
  · have hnat1 : Z.ncard ≤ ∑ᶠ s ∈ Z, analyticOrderNatAt riemannZeta s := by
      rw [Set.ncard_eq_toFinset_card Z hZfin, finsum_mem_eq_finite_toFinset_sum _ hZfin]
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun s hs => by
        have hsZ : s ∈ Z := (Set.Finite.mem_toFinset hZfin).mp hs
        have h := Zeta23.zetaSeam.one_le_mult s ⟨hsZ.1, hsZ.2.1, hsZ.2.2.1⟩
        simpa only [Zeta23.zeroMult, analyticOrderNatAt] using h
    have hnat2 : ∑ᶠ s ∈ Z, analyticOrderNatAt riemannZeta s ≤
        ∑ᶠ s ∈ W, analyticOrderNatAt riemannZeta s := by
      rw [finsum_mem_eq_finite_toFinset_sum _ hZfin,
        finsum_mem_eq_finite_toFinset_sum _ hWfin]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro x hx
        exact (Set.Finite.mem_toFinset hWfin).mpr
          (hZsubW ((Set.Finite.mem_toFinset hZfin).mp hx))
      · intro x _ _
        exact Nat.zero_le _
    have hreal : (Z.ncard : ℝ) ≤ (10 : ℝ) ^ 10 := by
      calc (Z.ncard : ℝ)
          ≤ ((∑ᶠ s ∈ Z, analyticOrderNatAt riemannZeta s : ℕ) : ℝ) := by
            exact_mod_cast hnat1
        _ = ∑ᶠ s ∈ Z, (analyticOrderNatAt riemannZeta s : ℝ) :=
            Nat.cast_finsum_mem hZfin _
        _ ≤ ∑ᶠ s ∈ W, (analyticOrderNatAt riemannZeta s : ℝ) := by
            rw [← Nat.cast_finsum_mem hZfin, ← Nat.cast_finsum_mem hWfin]
            exact_mod_cast hnat2
        _ ≤ (10 : ℝ) ^ 10 := hcount
    exact_mod_cast hreal
