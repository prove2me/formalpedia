-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.coeffIn_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:33:57.788211+00:00
-- url     : https://prove2.me/submissions/b92074a6-5ad3-4953-bdef-3a208f371f8a

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
theorem _root_.solution {m : ℕ} {p q : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B}
    (hp : CoeffIn W m p) (hq : CoeffIn W m q) : CoeffIn W m (p + q) := fun β => by
  rw [coeff_add]
  exact Submodule.add_mem _ (hp β) (hq β)
end ReciprocityTheory.ChartRestriction.G.T0
