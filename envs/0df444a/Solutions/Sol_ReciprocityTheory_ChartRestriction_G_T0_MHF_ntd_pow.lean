-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.MHF.ntd_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:29:11.122034+00:00
-- url     : https://prove2.me/submissions/3b02e73a-919b-487e-8e64-3f28a060b368

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffPsiBNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.MHF
open MvPolynomial ReciprocityTheory.MultiplicativeHeights
variable {K : Type*} [Field K] {B n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.MHF
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] (p : Polynomial R) (hp : p ≠ 0) (m : ℕ) :
    (p ^ m).natTrailingDegree = m * p.natTrailingDegree := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Polynomial.natTrailingDegree_mul (pow_ne_zero _ hp) hp, ih, Nat.succ_mul]
end ReciprocityTheory.ChartRestriction.G.T0.MHF
