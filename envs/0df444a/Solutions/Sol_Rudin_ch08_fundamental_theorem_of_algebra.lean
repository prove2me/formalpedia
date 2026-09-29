-- Prove2me | solution 1 for Rudin.ch08_fundamental_theorem_of_algebra
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:38:16.606131+00:00
-- url     : https://prove2.me/submissions/5e9b89e9-0bc7-450e-b99e-2e713c123467

import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic
open Filter Topology
noncomputable section
set_option maxHeartbeats 1000000
/-- Rudin, Theorem 8.8 (fundamental theorem of algebra): every nonconstant complex polynomial
has a root. -/
theorem solution (n : ℕ) (hn : 1 ≤ n) (a : ℕ → ℂ) (han : a n ≠ 0) :
    ∃ z : ℂ, ∑ k ∈ Finset.range (n + 1), a k * z ^ k = 0 := by
  classical
  let p : Polynomial ℂ := ∑ k ∈ Finset.range (n + 1), Polynomial.monomial k (a k)
  have hp : p.coeff n = a n := by
    simp [p, Polynomial.coeff_sum, Polynomial.coeff_monomial]
  have hnpos : 0 < p.natDegree := lt_of_lt_of_le (by omega) (Polynomial.le_natDegree_of_ne_zero (hp ▸ han))
  obtain ⟨z, hz⟩ := Complex.exists_root (Polynomial.natDegree_pos_iff_degree_pos.mp hnpos)
  refine ⟨z, ?_⟩
  simpa [Polynomial.IsRoot, p, Polynomial.eval_finset_sum] using hz
#print axioms solution
