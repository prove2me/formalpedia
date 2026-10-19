-- Prove2me | solution 1 for PermanentRollout.zeroLocus_gradientIdeal_eq_criticalLocus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/16f13700-e9a5-4667-9d22-0ad31375ce12

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_criticalLocus_eq_zeroLocus_pderiv_span

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace PermanentRollout
theorem _root_.solution {m : ℕ}
    (P : MvPolynomial (Fin m) ℂ) :
    MvPolynomial.zeroLocus ℂ
        (homogeneousMapIdeal (fun i : Fin m => MvPolynomial.pderiv i P)) =
      criticalLocus P := by
  simpa [homogeneousMapIdeal] using
    (criticalLocus_eq_zeroLocus_pderiv_span P).symm
end PermanentRollout
