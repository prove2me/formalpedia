-- Prove2me | solution 1 for PI.BesselDerivW.liftA_apply
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:43:03.838932+00:00
-- url     : https://prove2.me/submissions/176b52aa-2fe9-400b-b757-6ca7a31660f0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselDerivatives_LiftAOneZero
import Mathlib


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
noncomputable section
open PI PI.BesselDerivW
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
theorem _root_.solution (a : E →L[ℝ] E) (p : ℝ × E) : liftA a p = (0, a p.2) := by
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
  trace "HIT_62_0"

end 
