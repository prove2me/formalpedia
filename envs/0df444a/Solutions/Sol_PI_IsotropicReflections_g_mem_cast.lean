-- Prove2me | solution 1 for PI.IsotropicReflections.g_mem_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:56:29.396942+00:00
-- url     : https://prove2.me/submissions/e2d80906-b256-4803-9f12-66d734916e4c

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylConjugationFixedColumn_ReflectionScalarDualIsotropic

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
theorem _root_.solution : g ∈ Glev k r l.castSucc := by
  have h := hg
  simp only [Glev, Set.mem_setOf_eq] at h ⊢
  refine ⟨h.1, fun a ha => h.2 a ?_⟩
  simp only [Fin.coe_castSucc, Fin.val_succ] at ha ⊢
  omega
end PI.IsotropicReflections
