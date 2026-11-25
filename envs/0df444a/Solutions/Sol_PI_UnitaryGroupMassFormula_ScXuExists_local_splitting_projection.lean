-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.local_splitting_projection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:32:19.589635+00:00
-- url     : https://prove2.me/submissions/c78d4052-cb23-4f41-9542-4c16879ba3ef

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SplitGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_NatCastTmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SplitLoc
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_locSplitP_dec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution : LocSplitP := by
  intro I g r k e f Rf v hsum
  obtain ⟨p1, hp, -⟩ := locSplitP_dec I g r k e f Rf v hsum
  exact ⟨p1, hp⟩
end PI.UnitaryGroupMassFormula.ScXuExists
