-- Prove2me | solution 1 for RobustLP.Counterpart.rc_extension_of_beta
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:25:18.786635+00:00
-- url     : https://prove2.me/submissions/1c16ef63-767c-436b-93b3-0b70472d1d94

import Mathlib
import Definitions.Def_RobustLP_Counterpart_UncertainLP
import Definitions.Def_RobustLP_Counterpart_RobustCounterparts
open scoped BigOperators

namespace RobustLP.Counterpart

/-- **Sufficient condition for extending `x` to (RC)** (Ben-Tal–Nemirovski 2000, §3.1, p. 420).
For `ε > 0`, `δ > 0`, `Ω > 0`: if `x` is feasible for (LP) and
`∑_j a_{ij} x_j + ε β_i(x) ≤ b_i + δ max[1, |b_i|]` for every `i`, where
`β_i(x) = Ω √(∑_{j ∈ J_i} a_{ij}² x_j²)`, then `x` extends to a feasible solution `(x, y, z)` of
(RC[ε, δ, Ω]). -/
theorem _root_.solution {n p m : ℕ} (L : UncertainLP n p m)
    (ε δ Ω : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hΩ : 0 < Ω) (x : Fin n → ℝ)
    (hLP : L.NominalFeasible x)
    (hβ : ∀ i : Fin m, ∑ j, L.A i j * x j +
      ε * (Ω * Real.sqrt (∑ j ∈ L.J i, L.A i j ^ 2 * x j ^ 2)) ≤ L.bPlus δ i) :
    ∃ y z : Fin m → Fin n → ℝ, L.RCFeasible ε δ Ω x y z := by
  refine ⟨fun _ _ => 0, fun _ j => x j, hLP.1, hLP.2.1, ?_, hLP.2.2, ?_⟩
  · simpa using hβ
  · intro i j; simp

end RobustLP.Counterpart
