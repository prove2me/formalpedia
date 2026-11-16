-- Prove2me | solution 1 for PHIP1887.atom_border
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:53:26.642696+00:00
-- url     : https://prove2.me/submissions/e2ca8d11-9530-4264-9343-1c29560cbf15

import Mathlib
import Definitions.Def_RHPF28_PHIP1887_6e42e337ddd5
open MeasureTheory Set
open PHIP1887

theorem solution (y : ℂ) (p : ℕ) : atom y p 0 = y^p := by
  simp [atom]
