-- Prove2me | solution 1 for PHarmonicPoly.deficit_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:47:06.123641+00:00
-- url     : https://prove2.me/submissions/80d37561-9cad-4419-9966-56860b2b5845

module
public import Definitions.Def_PHarmonicPoly
public import Definitions.Def_PHarmonicPoly_Solution
public import Theorems.Thm_DeficitBound


set_option autoImplicit false
@[expose] public section
public section
open PHarmonicPoly
namespace PHarmonicPoly
theorem _root_.solution {m : ℕ} (hm : 2 ≤ m) {T : ℝ → ℝ} (hT : TrigPolyLe m T)
    (hbd : ∀ t : ℝ, |T t| ≤ 1) (h0 : T 0 = 1) :
    (0 ≤ 1 + T (Real.pi / m) ∧ 0 ≤ 1 + T (-(Real.pi / m)))
      ∧ (1 + T (Real.pi / m)
            ≤ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m))
          ∧ 1 + T (-(Real.pi / m))
            ≤ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m)))
      ∧ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m))
          ≤ Real.pi ^ 2 * ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) / (2 * (m : ℝ) ^ 2) :=
  _root_.DeficitBound hm hT hbd h0
end PHarmonicPoly
