-- Prove2me | solution 1 for P2M_summable_iff_bounded__0805d0f98b94
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:34:20.75396+00:00
-- url     : https://prove2.me/submissions/edc79425-da38-45d5-b189-ca365a3b9590

import Definitions.Def_PrimeNumberTheoremAnd_Wiener

open BigOperators Filter Asymptotics

set_option autoImplicit false in
theorem solution {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, 0 ≤ u n) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  constructor
  · intro h
    exact h.hasSum.tendsto_sum_nat.isBigO_one ℝ
  · intro h
    obtain ⟨C, hC⟩ := Asymptotics.isBigO_one_nat_atTop_iff.mp h
    obtain ⟨N, hN⟩ := eventually_atTop.1 hu
    apply (summable_nat_add_iff N).mp
    apply summable_of_sum_range_le (c := C + C)
    · intro n
      exact hN (n + N) (Nat.le_add_left N n)
    · intro n
      have htail : (∑ i ∈ Finset.range n, u (i + N)) =
          cumsum u (n + N) - cumsum u N := by
        simp only [cumsum]
        rw [Nat.add_comm n N, Finset.sum_range_add]
        simp only [Nat.add_comm N]
        abel
      rw [htail]
      calc
        cumsum u (n + N) - cumsum u N ≤ ‖cumsum u (n + N) - cumsum u N‖ :=
          Real.le_norm_self _
        _ ≤ ‖cumsum u (n + N)‖ + ‖cumsum u N‖ := norm_sub_le _ _
        _ ≤ C + C := add_le_add (hC _) (hC _)
