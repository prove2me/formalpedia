-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.scU_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:53.579033+00:00
-- url     : https://prove2.me/submissions/72aa5727-858f-4879-8457-c6df4433de2b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open PI PI.UnitaryApproxFinWork
variable {n : Type} [Fintype n] [DecidableEq n]
namespace PI.UnitaryApproxFinWork
theorem _root_.solution {A : Type} [CommRing A] (a b : A) (h : a * b = 1) :
    ((scU (n := n) a b h : GL n A) : Matrix n n A) = a • 1 := rfl
end PI.UnitaryApproxFinWork
