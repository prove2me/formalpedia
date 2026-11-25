-- Prove2me | solution 1 for PI.Residue.boxVolume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:18:35.043741+00:00
-- url     : https://prove2.me/submissions/226b7039-f833-4af5-ad21-851fb1b8fadf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BoxEqConvexBodyLT
import Theorems.Thm_PI_Residue_box_eq_convexBodyLT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped ENNReal Classical
noncomputable section
open PI PI.Residue
namespace PI.Residue
theorem _root_.solution : BoxVolume := by
  intro K _ _ r hr
  rw [box_eq_convexBodyLT K r hr, convexBodyLT_volume, vfac]
  congr 1
  rw [ENNReal.ofReal_prod_of_nonneg (fun w _ => (pow_pos (hr w) _).le)]
  push_cast
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [ENNReal.ofReal_pow (hr w).le]
  rfl
end PI.Residue
