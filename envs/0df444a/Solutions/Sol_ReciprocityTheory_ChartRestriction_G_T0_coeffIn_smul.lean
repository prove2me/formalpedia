-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.coeffIn_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:14:49.857598+00:00
-- url     : https://prove2.me/submissions/2de3eed8-25ae-457d-b6ea-daed310d2a2f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SumLeSqrtCardMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffEvWMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Algebra R B] {D N : ℕ}
variable (W : Submodule R B)
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {m : ℕ} {p : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B}
    (hp : CoeffIn W m p) (r : R) : CoeffIn W m (C (algebraMap R B r) * p) := fun β => by
  rw [coeff_C_mul, ← Algebra.smul_def]
  exact Submodule.smul_mem _ r (hp β)
end ReciprocityTheory.ChartRestriction.G.T0
