-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DLm.gN_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:36.142397+00:00
-- url     : https://prove2.me/submissions/142fc6b3-6fdc-44ab-b449-8bc9aba5b307

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFibreBoundDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnitaryWeylCompact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PointwiseBoundHolds
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_cornerA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_cornerB
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_ell
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_fromCols
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_fromRows
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_lowW
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_strictUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_subS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_supS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_continuous_psi_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_cornerA
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_cornerB
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_ell
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_fromCols
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_fromRows
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_lowW
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_strictUpper
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_subS
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_supS
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_upper
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.continuous_psi_comp



set_option autoImplicit false
open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DLm
namespace PI.UnitaryGroupMassFormula.DLm
theorem _root_.solution (k r : ℕ) : Continuous (fun g : B.Mat k r => B.gN g) := by
  unfold B.gN
  fun_prop
end PI.UnitaryGroupMassFormula.DLm
