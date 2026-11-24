-- Prove2me | solution 1 for PI.LowUniSplit.first_factor_mem_lower_triangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:42:33.404603+00:00
-- url     : https://prove2.me/submissions/d4918c49-5d02-406e-be55-6e4655a88c27

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerUnipotentSplit_SecondFactorMemLowerTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.LowUniSplit
open Formalism.FourierDecayAlt.C2
variable {m : ℕ}
variable (S : Fin m → Fin m → Prop) [DecidableRel S] (l : Matrix (Fin m) (Fin m) ℂ)
namespace PI.LowUniSplit
theorem _root_.solution : fac1 S l ∈ LTset m := by
  refine ⟨fun i j h => ?_, fun i => by simp [fac1]⟩
  simp [fac1, ne_of_lt h, not_lt.mpr h.le]
end PI.LowUniSplit
