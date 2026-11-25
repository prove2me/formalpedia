-- Prove2me | solution 1 for PI.Dv.GLatHermW.isCM_cf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:10:31.057751+00:00
-- url     : https://prove2.me/submissions/4e901c40-4ad9-480e-b7ca-fbec319ee90b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_AsAlgebraHomEG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_IsCMFormEOf
import Theorems.Thm_PI_Dv_GLatHermW_star_cf
import Theorems.Thm_PI_Dv_GLatHermW_star_map_cf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLatHermW
open PI.Dv Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.GLatHermW
theorem _root_.solution (hS : StarIsConj K) (T : GoodSet K G) (g : G) : IsCM (cf T g) := by
  intro σ
  rw [star_cf hS, star_map_cf]
end PI.Dv.GLatHermW
