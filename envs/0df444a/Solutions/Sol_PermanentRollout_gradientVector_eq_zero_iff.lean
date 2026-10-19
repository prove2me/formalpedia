-- Prove2me | solution 1 for PermanentRollout.gradientVector_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/76445775-9f33-4aef-82b6-0db2f4343274

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace PermanentRollout
theorem _root_.solution {m : ℕ}
    (P : MvPolynomial (Fin m) ℂ) (v : Fin m → ℂ) :
    gradientVector P v = 0 ↔ v ∈ criticalLocus P := by
  simp [gradientVector, criticalLocus, funext_iff]
end PermanentRollout
