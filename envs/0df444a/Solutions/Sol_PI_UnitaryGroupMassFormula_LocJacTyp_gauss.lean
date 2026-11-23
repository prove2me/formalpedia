-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.gauss
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:13.988871+00:00
-- url     : https://prove2.me/submissions/53a9a951-9f39-4bec-82d1-ace3ad140662

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ExpProductSquareInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp
open scoped Classical
namespace PI.UnitaryGroupMassFormula.LocJacTyp
theorem _root_.solution (r : ℕ) : 2 * ∑ i : Fin (r + 1), ((i : ℕ) : ℝ) = (r : ℝ) * (r + 1) := by
  have h := Finset.sum_range_id_mul_two (r + 1)
  rw [Fin.sum_univ_eq_sum_range (fun n => (n : ℝ)) (r + 1)]
  have h2 : ((∑ i ∈ Finset.range (r + 1), i : ℕ) : ℝ) * 2 = ((r + 1) * (r + 1 - 1) : ℕ) := by
    exact_mod_cast h
  push_cast at h2
  linarith
end PI.UnitaryGroupMassFormula.LocJacTyp
