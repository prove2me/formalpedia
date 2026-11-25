-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.cT_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:44:34.77323+00:00
-- url     : https://prove2.me/submissions/9a83c6c9-0bd0-48fa-b53e-90a630ea94e4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_ClassFiniteOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_PosDefOfDefiniteSignatureHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution {m : Type} (X : Matrix m m ℂ) : cT (starRingEnd ℂ) X = Xᴴ := by
  unfold PI.UJClassFin.cT
  ext i j
  rfl
end PI.UnitaryGroupMassFormula.UJClassFin
