-- Prove2me | solution 1 for PHIP1887.real_atom_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:46:55.035949+00:00
-- url     : https://prove2.me/submissions/46707330-20bb-435e-b13a-b3254de61430

import Mathlib
import Definitions.Def_RHPF28_PHIP1887_6e42e337ddd5
open MeasureTheory Set
open PHIP1887

theorem solution (r : ℝ) (p q : ℕ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    0 ≤ (atom (r : ℂ) p q).re := by
  simp only [atom, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (pow_nonneg h0 _) (pow_nonneg (sub_nonneg.mpr h1) _)
