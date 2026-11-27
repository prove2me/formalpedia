-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.iteratedDeriv_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:26:35.686313+00:00
-- url     : https://prove2.me/submissions/f99b4110-9afa-4929-b2cf-3613c87c93b8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_OwnerNoneIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IteratedDerivListBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
variable {E : Type} [Field E] [NumberField E] {n nb : ℕ}
variable {dim : (E →+* ℂ) → ℕ}
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (s : (Fin 1 → Vsp dim) → ℂ) {N M : ℕ} (h : N = M) (v : Fin N → Vsp dim) :
    d1 s N v = d1 s M (fun k => v (k.cast h.symm)) := by
  subst h
  rfl
end ReciprocityTheory.ChartRestriction.G.I2
