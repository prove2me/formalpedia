-- Prove2me | solution 1 for PI.IsotropicReflections.hpk_s_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:42:32.118384+00:00
-- url     : https://prove2.me/submissions/2e7827b2-3782-45ef-b753-6a706945babc

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
theorem _root_.solution (l : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r l) j = if j = eI k r l then 1 else 0 := by
  have hl := l.isLt
  have hj := j.isLt
  simp only [Hpk]
  split_ifs <;> (try simp only [Fin.ext_iff, eI_val_weyl_conjugation_fixed_column, esI_val'] at *) <;> first | rfl | omega
end PI.IsotropicReflections
