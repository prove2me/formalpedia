-- Prove2me | solution 1 for PermanentRollout.eval_deletedCoordinateEsymmPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/6d786d04-b4a7-4e00-9452-3a66a9712156

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {t : ℕ}
    (u : Fin t → ℂ) (i : Fin t) (q : ℕ) :
    MvPolynomial.eval u (deletedCoordinateEsymmPolynomial t q i) =
      deletedCoordinateEsymm u i q := by
  classical
  simp only [deletedCoordinateEsymmPolynomial, deletedCoordinateEsymm,
    Finset.esymm_map_val, map_sum, map_prod, MvPolynomial.eval_X]
end PermanentRollout
