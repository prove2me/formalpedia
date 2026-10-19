-- Prove2me | solution 1 for PermanentRollout.mk_mem_projectiveCriticalLocus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/07f8856f-1cc0-450f-a7c0-45ac3f555aec

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
    (P : MvPolynomial (Fin m) ℂ) (v : Fin m → ℂ)
    (hv : v ≠ 0) (hcritical : v ∈ criticalLocus P) :
    Projectivization.mk ℂ v hv ∈ projectiveCriticalLocus P :=
  ⟨v, hv, rfl, hcritical⟩
end PermanentRollout
