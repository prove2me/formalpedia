-- Prove2me | solution 1 for PI.CompAtExist.muV_int_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:27.883783+00:00
-- url     : https://prove2.me/submissions/285813f1-8050-49ed-9851-49732e22237e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_UniROfUniRT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionExistence_LeOneIffOfMulEqOne
import Theorems.Thm_PI_CompAtExist_muV_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CompAtExist
open NumberField IsDedekindDomain ReciprocityTheory.Aut
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
namespace PI.CompAtExist
theorem _root_.solution (s : SplitPlace L) (r : 𝓞 L) : muV s (algebraMap (𝓞 L) L r) ≤ 1 := by
  rw [muV_apply]
  have := s.split_le_one r
  rwa [RingOfIntegers.coe_eq_algebraMap] at this
end PI.CompAtExist
