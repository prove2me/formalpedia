-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.wa_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:20:51.024084+00:00
-- url     : https://prove2.me/submissions/51a35e7d-fb14-4669-9730-7dba964a23e6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Filter
variable {F : Type*} [Field F]
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (w : AddValuation F (WithTop ℤ)) {a : F} {m : ℤ} (h : w a = m) (n : ℕ) :
    w (a ^ n) = ((n * m : ℤ) : WithTop ℤ) := by
  induction n with
  | zero =>
    rw [pow_zero, AddValuation.map_one]
    simp
  | succ k ih =>
    rw [pow_succ, AddValuation.map_mul, ih, h, ← WithTop.coe_add]
    congr 1
    push_cast
    ring
end ReciprocityTheory.ChartRestriction.G.T0
