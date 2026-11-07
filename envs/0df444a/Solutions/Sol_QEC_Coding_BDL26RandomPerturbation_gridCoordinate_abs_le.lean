-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.gridCoordinate_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:57:13.259176+00:00
-- url     : https://prove2.me/submissions/89900ba9-265e-401b-977b-09a4e4d2f40e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridPointQuery

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (K : ℕ) (g : GridCoordinate K) : g.val.natAbs ≤ K := by
  have h := Finset.mem_Icc.mp g.property
  have hlo := h.1
  have hhi := h.2
  have ha : |g.val| ≤ (K : ℤ) := abs_le.mpr h
  have he : (g.val.natAbs : ℤ) = |g.val| := Int.natCast_natAbs g.val
  rw [← he] at ha
  exact_mod_cast ha
end QEC.Coding.BDL26RandomPerturbation
