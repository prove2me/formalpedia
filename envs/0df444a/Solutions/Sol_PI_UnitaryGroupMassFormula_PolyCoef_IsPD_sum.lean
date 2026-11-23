-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PolyCoef.IsPD.sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:57.296498+00:00
-- url     : https://prove2.me/submissions/2a768966-9e97-43f8-bee1-e966dbecca02

import Mathlib
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi25_sum__8f7927b3f793
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PolyCoef
open MeasureTheory Matrix
namespace PI.UnitaryGroupMassFormula.PolyCoef
namespace IsPD
theorem _root_.solution {N : ℕ} {ι : Type*} (s : Finset ι) {F : ι → UG N → ℂ} (hF : ∀ i ∈ s, IsPD (F i)) :
    IsPD (fun g => ∑ i ∈ s, F i g) := by
  first | exact P2M_UpperTheory_Reformulated_B_Qi25_sum__8f7927b3f793 .. | (apply P2M_UpperTheory_Reformulated_B_Qi25_sum__8f7927b3f793 <;> assumption) | (intros; apply P2M_UpperTheory_Reformulated_B_Qi25_sum__8f7927b3f793 <;> assumption) | (apply @P2M_UpperTheory_Reformulated_B_Qi25_sum__8f7927b3f793 <;> assumption) | (intros; apply @P2M_UpperTheory_Reformulated_B_Qi25_sum__8f7927b3f793 <;> assumption) | (apply @P2M_UpperTheory_Reformulated_B_Qi25_sum__8f7927b3f793 <;> first | assumption | infer_instance) | exact @P2M_UpperTheory_Reformulated_B_Qi25_sum__8f7927b3f793 N ι s F hF | exact @P2M_UpperTheory_Reformulated_B_Qi25_sum__8f7927b3f793 N ι s F | exact @P2M_UpperTheory_Reformulated_B_Qi25_sum__8f7927b3f793 N ι s | exact @P2M_UpperTheory_Reformulated_B_Qi25_sum__8f7927b3f793 N ι | exact @P2M_UpperTheory_Reformulated_B_Qi25_sum__8f7927b3f793 N
end IsPD
end PI.UnitaryGroupMassFormula.PolyCoef
