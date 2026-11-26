-- Prove2me | solution 1 for PositivityTheory.ThKR.Sieg.Heis.mul_def
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:59:33.788886+00:00
-- url     : https://prove2.me/submissions/49870fe6-5063-4ff8-b55c-eb71951d2b61

import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmulNn
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_SiegelHaar
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
import Mathlib





-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory MeasureTheory.Measure Topology Set
open scoped NNReal ENNReal Pointwise
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Sieg
variable {A B : Type} [AddCommGroup A] [AddCommGroup B]
variable (β : A →+ A →+ B)
theorem _root_.solution (x y : Heis β) : x * y = (x.1 + y.1, x.2 + y.2 + β x.1 y.1) := by
  first
    | (intros; rfl)
    | exact Iff.rfl
    | decide
    | (intros; omega)
    | (intros; simp)
    | (intros; simp_all)
    | (intros; norm_num)
    | (intros; positivity)
    | (intros; aesop)
    | (intros; nlinarith)
    | (intros; field_simp; ring)
    | (intros; ext; simp)
    | (intros; constructor <;> intro h <;> simpa using h)
    | (intros; exact?)
  trace "HIT_65_1"

end 
