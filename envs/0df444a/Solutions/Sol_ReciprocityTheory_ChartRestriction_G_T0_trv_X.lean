-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.trv_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:53:16.498971+00:00
-- url     : https://prove2.me/submissions/05bd5e59-9083-45c7-a403-01229d83f351

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZEqConstMulIrreduciblePow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RelationMapCommTransvection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {R : Type*} [CommRing R] {D N : ℕ} (i k : Fin (D + 1))
    (e : Polynomial (MvPolynomial (TVar D N) R)) (t : TVar D N) :
    trv i k e (X t) = if t.1 = i then Polynomial.C (X t) + e * Polynomial.C (X (k, t.2))
      else Polynomial.C (X t) := by
  unfold trv
  rw [MvPolynomial.aeval_X]
end ReciprocityTheory.ChartRestriction.G.T0
