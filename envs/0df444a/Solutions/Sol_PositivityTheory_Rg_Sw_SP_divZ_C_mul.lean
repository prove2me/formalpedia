-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.divZ_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:40.492879+00:00
-- url     : https://prove2.me/submissions/d0f65880-f024-4b42-94c9-0fe59fa71656

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open Polynomial
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution {n : ℕ} (i : ℕ) (p : Polynomial ℂ) (R : Fm n) (h : (X : Polynomial ℂ) ^ i ∣ p) :
    DivZ i (MvPolynomial.C p * R) := by
  intro e
  rw [MvPolynomial.coeff_C_mul]
  exact Dvd.dvd.mul_right h _
end PositivityTheory.Rg.Sw.SP
