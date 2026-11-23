-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.cT_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:53.413262+00:00
-- url     : https://prove2.me/submissions/d6e75ab5-4d65-4a04-9b38-51fe1b811799

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_Cayley

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.UnitaryApproxFinWork
variable {n : Type} [Fintype n] [DecidableEq n] {A : Type} [CommRing A] (ρ : A →+* A)
namespace PI.UnitaryApproxFinWork
theorem _root_.solution (M N : Matrix n n A) : PI.UnitaryApproxDefs.cT ρ (M - N) = PI.UnitaryApproxDefs.cT ρ M - PI.UnitaryApproxDefs.cT ρ N := by
  ext i j
  simp [PI.UnitaryApproxDefs.cT]
end PI.UnitaryApproxFinWork
