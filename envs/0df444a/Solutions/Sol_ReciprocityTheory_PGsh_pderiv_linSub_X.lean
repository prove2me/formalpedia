-- Prove2me | solution 1 for ReciprocityTheory.PGsh.pderiv_linSub_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:49:02.51048+00:00
-- url     : https://prove2.me/submissions/79e0ddd2-2322-4869-82f0-09149077ed59

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh
variable {n : ℕ}
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.PGsh
theorem _root_.solution (g : Matrix (Fin n) (Fin n) R) (a b : Fin n) (v : Fin n × Fin n) :
    pderiv (a, b) (linSub g (X v)) = if v.2 = b then C (g v.1 a) else 0 := by
  simp only [linSub, aeval_X, map_sum, Derivation.leibniz, pderiv_C, pderiv_X, smul_zero,
    add_zero, smul_eq_mul, Pi.single_apply, Prod.mk.injEq]
  by_cases hb : v.2 = b
  · subst hb; simp
  · simp [hb]
end ReciprocityTheory.PGsh
