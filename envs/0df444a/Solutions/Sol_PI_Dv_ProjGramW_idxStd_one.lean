-- Prove2me | solution 1 for PI.Dv.ProjGramW.idxStd_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:55.065042+00:00
-- url     : https://prove2.me/submissions/0f9aa912-f13f-481d-92ef-36071666ea1b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
import Theorems.Thm_PI_Dv_ProjGramW_famC_one
import Theorems.Thm_PI_Dv_ProjGramW_idx_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (d : ℕ) :
    idxStd w (1 : Matrix (Fin d) (Fin d) K) = 0 := by
  unfold idxStd
  rw [famC_one]
  exact idx_self hI w (Submodule.fg_span (Set.finite_range _))
end PI.Dv.ProjGramW
