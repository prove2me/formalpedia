-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FormPartialDerivatives.perpVec_of_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:07.206164+00:00
-- url     : https://prove2.me/submissions/4c26f6ff-f3b7-4916-a50c-d7ae0ce5bfe3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_PerpVecPerpSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_PerpendicularDeterminants_PerpVecOfPerp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FormPartialDerivatives
open ReciprocityTheory.ChartRestriction.G.TB
namespace PI.UnitaryGroupMassFormula.FormPartialDerivatives
theorem _root_.solution (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (p : ℕ)
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) (hg : ∀ a, h g (e a) = 0) :
    perpVec h e e' g = (hMat h e e').det • g := by
  simp [perpVec, hg]
end PI.UnitaryGroupMassFormula.FormPartialDerivatives
