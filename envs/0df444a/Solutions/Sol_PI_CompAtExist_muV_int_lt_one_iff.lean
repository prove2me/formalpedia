-- Prove2me | solution 1 for PI.CompAtExist.muV_int_lt_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:27.918932+00:00
-- url     : https://prove2.me/submissions/5e113521-87dd-4680-a9ed-875d467ac548

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
theorem _root_.solution (s : SplitPlace L) (r : 𝓞 L) :
    muV s (algebraMap (𝓞 L) L r) < 1 ↔ r ∈ s.w.asIdeal := by
  rw [muV_apply, show s.w.asIdeal = s.ideal from rfl, s.split_mem_ideal, RingOfIntegers.coe_eq_algebraMap]
end PI.CompAtExist
