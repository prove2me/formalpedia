-- Prove2me | solution 1 for PI.IsotropicReflections.eI_ne_esI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:15:49.706056+00:00
-- url     : https://prove2.me/submissions/745ac6b4-6daf-4d04-95f9-8cc73b3e8c61

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
section
open Matrix Finset
noncomputable section
namespace PI.IsotropicReflections
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
variable {k r : ℕ}
private lemma eI_val_weyl_conjugation_fixed_column (l : Fin r) : (eI k r l).val = l.val := rfl
private lemma esI_val' (l : Fin r) : (esI k r l).val = 2 * r + k - l.val := rfl
section G
variable (l : Fin r) (g : Mx k r) (hg : g ∈ Glev k r l.succ)
include hg
end G
end PI.IsotropicReflections
end
end

set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.IsotropicReflections
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
variable {k r : ℕ}
namespace PI.IsotropicReflections
theorem _root_.solution (l : Fin r) : eI k r l ≠ esI k r l := by
  intro h
  have h' := congrArg Fin.val h
  rw [eI_val_weyl_conjugation_fixed_column, esI_val'] at h'
  have := l.isLt
  omega
end PI.IsotropicReflections
