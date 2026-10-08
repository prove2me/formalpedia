-- Prove2me | solution 1 for UnrelatedSched.FixedMachines.combined_load_le
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:48:36.377635+00:00
-- url     : https://prove2.me/submissions/ec5d29e8-3481-466b-9abd-88a147a3b01c

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_FixedMachines_LongAssignment
open UnrelatedSched.FixedMachines MatousekLP.Scheduling


open MatousekLP.Scheduling

/-- §3, p. 6: if the schedule `σ` agrees with the schedule of long assignments `L` on the long
jobs and the short assignments take at most `d - t_i + ε d` on every machine `i`, then every
machine `i` is busy for at most `t_i + d - t_i + ε d = (1 + ε) d`. -/
theorem solution {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (hP : ∀ i j, 0 < P i j) (ε : ℝ) (hε : 0 < ε) (d : ℕ) (L : Fin n → Option (Fin m))
    (σ : Fin n → Fin m) (hfollow : ∀ j i, L j = some i → σ j = i)
    (hshort : ∀ i, shortLoad P L σ i ≤ (d : ℝ) - longLoad P L i + ε * (d : ℝ)) :
    ∀ i, load (fun i j => (P i j : ℝ)) σ i ≤ (1 + ε) * (d : ℝ) := by
  classical
  intro i
  have heq : load (fun i j => (P i j : ℝ)) σ i = longLoad P L i + shortLoad P L σ i := by
    simp only [load, longLoad, shortLoad, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    cases hl : L j with
    | none => simp [hl]
    | some a =>
      have hf := hfollow j a hl
      by_cases ha : a = i
      · simp [hl, hf, ha]
      · have hsi : σ j ≠ i := by simpa [hf] using ha
        simp [hl, ha, hsi]
  rw [heq]
  have hh := hshort i
  nlinarith



#print axioms solution
