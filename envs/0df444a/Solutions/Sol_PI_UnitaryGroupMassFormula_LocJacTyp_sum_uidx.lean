-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.sum_uidx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:14.075012+00:00
-- url     : https://prove2.me/submissions/d1451b01-515c-4c67-807e-c93dd2e9ff5c

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
theorem _root_.solution (r : ℕ) (g : Fin (r + 1) × Fin (r + 1) → ℝ) :
    ∑ q : UIdx r, g q.1 = ∑ i : Fin (r + 1), ∑ j : Fin (r + 1), if i < j then g (i, j) else 0 := by
  rw [← Fintype.sum_prod_type', ← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) (fun p => g p)).symm
end PI.UnitaryGroupMassFormula.LocJacTyp
