-- Prove2me | solution 1 for PI.StabSplit.FixW.uOf_UW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:23.406883+00:00
-- url     : https://prove2.me/submissions/a19a8126-3a68-4fca-9b40-efd0f8457221

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_FixSub
import Theorems.Thm_PI_StabSplit_FixW_uOf_mem
import Theorems.Thm_PI_StabSplit_FixW_uOf_fix_out
import Theorems.Thm_PI_StabSplit_FixW_unipotent_part_fixes_vector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic
noncomputable section
open PI PI.StabSplit PI.StabSplit.FixW
namespace PI.StabSplit.FixW
theorem _root_.solution {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {g : B.Mat k r}
    (hg : g ∈ FixSet k r z) : uOf k r g ∈ UWset k r z := by
  refine ⟨uOf_mem hg, fun a => ⟨?_, ?_⟩, unipotent_part_fixes_vector hz hg⟩
  · exact uOf_fix_out g _ (Or.inl (by simp [eI]))
  · exact uOf_fix_out g _ (Or.inr (by simp [esI]; omega))
end PI.StabSplit.FixW
