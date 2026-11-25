-- Prove2me | solution 1 for PI.IsotropicReflections.reflection_mem_Glev_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:19:12.021534+00:00
-- url     : https://prove2.me/submissions/e23aee9d-8aca-45fa-ba4c-a2f7e31b3671

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylConjugationFixedColumn_ReflectionScalarDualIsotropic
import Theorems.Thm_PI_IsotropicReflections_reflection_mem_unitary
import Theorems.Thm_PI_IsotropicReflections_reflection_fixes_basis_vector
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
theorem _root_.solution (l : Fin r) (c : ℂ) (hc : c ≠ 0) : w1 k r l c ∈ Glev k r l.castSucc := by
  simp only [Glev, Set.mem_setOf_eq]
  refine ⟨reflection_mem_unitary l c hc, fun a ha => ?_⟩
  have hal : a.val < l.val := by simpa using ha
  have h1 := a.isLt
  have h2 := l.isLt
  refine ⟨reflection_fixes_basis_vector l c _ ?_ ?_, reflection_fixes_basis_vector l c _ ?_ ?_⟩ <;> intro h <;> have h' := congrArg Fin.val h <;>
    simp only [eI_val_weyl_conjugation_fixed_column, esI_val'] at h' <;> omega
end PI.IsotropicReflections
