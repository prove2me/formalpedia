-- Prove2me | solution 1 for PIW.AdelClassFin.gd_int_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:35:41.350863+00:00
-- url     : https://prove2.me/submissions/feca98f0-9d08-4832-826d-dd56cc3685f5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSmulRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorGramDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.UG NumberField
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [StarRing E] {m : ℕ} (J : Matrix (Fin m) (Fin m) E)
namespace PIW.AdelClassFin
theorem _root_.solution (c : ℤ) (x : Fin m → E) : ((c : E)) • x = ((c : ℚ)) • x := by
  rw [gd_qsmul, Rat.cast_intCast]
end PIW.AdelClassFin
