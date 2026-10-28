-- Prove2me | solution 1 for SolarTariff.Fair.proposition_5b_cs
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:39:57.89218+00:00
-- url     : https://prove2.me/submissions/2b7d9345-edff-429b-983b-2bd1f0e5f771

import Mathlib
import Definitions.Def_SolarTariff_Fair_Model

open SolarTariff.Fair in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Market ι) (hM : M.Standing) (A : Finset ι)
    (hA : Admissible M A) (hC : 0 ≤ dC M A) :
    objective M ((TStar M A).bills M) A (tm M A) ≤ 0 := by
  obtain ⟨hh, hd, hg, he, hcs, hdS⟩ := hM
  have hΔ : 0 < DeltaE M A :=
    Finset.sum_pos (fun i _ => mul_pos (hh i) (hg i)) hA.1
  have hE0 : 0 < E0 M :=
    Finset.sum_pos (fun i _ => mul_pos (hh i) (hd i)) Finset.univ_nonempty
  have hsum : ∑ i ∈ A, M.h i * M.g i * tStar M A i = tm M A * DeltaE M A := by
    unfold DeltaE
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    unfold tStar
    rw [if_pos hi]
    ring
  have htm : tm M A * DeltaE M A = M.cs (DeltaE M A) * DeltaE M A + M.dS := by
    unfold tm
    field_simp
  have hpr : prStar M A ≤ M.pr0 := by
    unfold prStar
    rw [div_le_iff₀ hE0, hsum, htm]
    unfold dC dWF at hC
    linarith
  unfold objective
  apply Finset.sup'_le
  intro i _
  unfold outflowChange
  simp only [T3.bills, TStar]
  by_cases hi : i ∈ A
  · rw [if_pos hi]
    unfold gridUsage tStar
    rw [if_pos hi]
    have e : prStar M A * (M.d i - (M.g i - M.e i)) - prStar M A * M.e i +
        M.g i * (prStar M A - tm M A) + tm M A * M.g i - M.pr0 * M.d i =
        (prStar M A - M.pr0) * M.d i := by ring
    rw [e]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hd i).le
  · rw [if_neg hi]
    have e : prStar M A * M.d i - M.pr0 * M.d i = (prStar M A - M.pr0) * M.d i := by ring
    rw [e]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hd i).le
