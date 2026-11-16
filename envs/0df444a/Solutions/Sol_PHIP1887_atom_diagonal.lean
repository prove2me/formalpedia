-- Prove2me | solution 1 for PHIP1887.atom_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:46:46.634721+00:00
-- url     : https://prove2.me/submissions/f6992599-078a-40de-bd3a-1e0a8671315b

import Mathlib
import Definitions.Def_RHPF28_PHIP1887_6e42e337ddd5
open MeasureTheory Set
open PHIP1887

theorem solution (y : ℂ) (k : ℕ) :
    atom y k k = (y*(1-y))^k := by
  simp [atom, mul_pow]
