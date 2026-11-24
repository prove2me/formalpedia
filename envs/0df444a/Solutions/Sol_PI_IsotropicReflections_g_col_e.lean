-- Prove2me | solution 1 for PI.IsotropicReflections.g_col_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:59:50.363492+00:00
-- url     : https://prove2.me/submissions/73608ad2-8bb3-447f-a3cb-c64189f08865

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylConjugationFixedColumn_ReflectionScalarDualIsotropic
import Theorems.Thm_PI_IsotropicReflections_mulVec_bvec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.IsotropicReflections
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
variable {k r : ℕ}
variable (l : Fin r) (g : Mx k r) (hg : g ∈ Glev k r l.succ)
include hg
namespace PI.IsotropicReflections
theorem _root_.solution (i : Fin (2 * r + k + 1)) : g i (eI k r l) = if i = eI k r l then 1 else 0 := by
  have h := hg
  simp only [Glev, Set.mem_setOf_eq] at h
  have e := (h.2 l (by simp)).1
  rw [mulVec_bvec] at e
  have e' := congrFun e i
  simpa [bvec, Pi.single_apply] using e'
end PI.IsotropicReflections
