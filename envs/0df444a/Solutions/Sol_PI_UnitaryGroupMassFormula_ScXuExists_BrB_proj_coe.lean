-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.BrB.proj_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:43:18.00878+00:00
-- url     : https://prove2.me/submissions/43dc7a02-9396-4a51-bd28-8a95203ef332

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitGL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondProjectionSplitEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.BrB
open Matrix PI.UnitaryGroupMassFormula.AdIndexEq
namespace PI.UnitaryGroupMassFormula.ScXuExists.BrB
theorem _root_.solution {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]
    (σ : R →+* R) (π : R ≃+* k × k) (J : Matrix n n R) (y : Formalism.UG.UJ σ J) :
    ((SplitGL.proj σ π J y : GL n k) : Matrix n n k) = ((y : GL n R) : Matrix n n R).map (SplitGL.p1 π) := rfl
end PI.UnitaryGroupMassFormula.ScXuExists.BrB
