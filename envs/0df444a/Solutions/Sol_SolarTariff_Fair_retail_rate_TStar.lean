-- Prove2me | solution 1 for SolarTariff.Fair.retail_rate_TStar
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:42:55.518864+00:00
-- url     : https://prove2.me/submissions/87d137b5-7ece-4a55-9a2b-1b7ea00c96f3

import Mathlib
import Definitions.Def_SolarTariff_Fair_Model

open SolarTariff.Fair in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Market ι) (hM : M.Standing) (A : Finset ι)
    (hA : Admissible M A) :
    prStar M A = M.pr0 - dC M A / E0 M ∧
      (0 ≤ dC M A → prStar M A ≤ M.pr0) := by
  obtain ⟨hh, hd, hg, _, _, _⟩ := hM
  have hΔ : 0 < DeltaE M A := Finset.sum_pos (fun i _ => mul_pos (hh i) (hg i)) hA.1
  have hE : 0 < E0 M :=
    Finset.sum_pos (fun i _ => mul_pos (hh i) (hd i)) ⟨hA.1.choose, Finset.mem_univ _⟩
  have hsum : ∑ i ∈ A, M.h i * M.g i * tStar M A i =
      M.cs (DeltaE M A) * DeltaE M A + M.dS := by
    have : ∀ i ∈ A, M.h i * M.g i * tStar M A i = M.h i * M.g i * tm M A := by
      intro i hi
      simp only [tStar, if_pos hi]
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul]
    change DeltaE M A * tm M A = _
    unfold tm
    rw [mul_add, mul_div_cancel₀ _ hΔ.ne']
    ring
  have h1 : prStar M A = M.pr0 - dC M A / E0 M := by
    unfold prStar dC dWF
    rw [hsum, eq_sub_iff_add_eq, ← add_div, div_eq_iff hE.ne']
    ring
  refine ⟨h1, fun h => ?_⟩
  rw [h1]
  have := div_nonneg h hE.le
  linarith
