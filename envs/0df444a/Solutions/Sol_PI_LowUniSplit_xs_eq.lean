-- Prove2me | solution 1 for PI.LowUniSplit.xs_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:42:17.098889+00:00
-- url     : https://prove2.me/submissions/ebe8c9f1-38fb-43b7-b238-bcd969bb9105

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
theorem _root_.solution (i j : Fin m) : xs S l i j = l i j - ∑ k : Btw i j,
    (if S i k.1 then xs S l i k.1 else 0) * (if S k.1 j then 0 else xs S l k.1 j) := by
  rw [xs]
end PI.LowUniSplit
