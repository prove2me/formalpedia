-- Prove2me | solution 1 for PI.DvRows.vAdd_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:09:37.863645+00:00
-- url     : https://prove2.me/submissions/283299e7-673a-4b2f-b864-e268de40b579

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
import Theorems.Thm_PI_DvRows_val_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.DvRows
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (x : K) : vAdd (conjW w) x = vAdd w (star x) := by
  unfold vAdd
  rw [val_conj]
end PI.DvRows
