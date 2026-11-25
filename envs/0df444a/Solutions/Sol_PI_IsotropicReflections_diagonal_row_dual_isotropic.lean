-- Prove2me | solution 1 for PI.IsotropicReflections.diagonal_row_dual_isotropic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:54:07.527903+00:00
-- url     : https://prove2.me/submissions/57658cda-ba3d-468a-8faa-da7d9bdae18b

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylConjugationFixedColumn_ReflectionScalarDualIsotropic
import Theorems.Thm_PI_IsotropicReflections_hpk_e_row
import Theorems.Thm_PI_IsotropicReflections_conj_fixed_col
import Theorems.Thm_PI_IsotropicReflections_g_col_e

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
theorem _root_.solution (j : Fin (2 * r + k + 1)) : g (esI k r l) j = if j = esI k r l then 1 else 0 := by
  have h := hg
  simp only [Glev, UH, Set.mem_setOf_eq] at h
  have e := conj_fixed_col g (Hpk k r) (eI k r l) (g_col_e l g hg) j
  rw [h.1] at e
  simp only [hpk_e_row, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at e
  exact e.symm
end PI.IsotropicReflections
