-- Prove2me | solution 1 for PI.StabSplit.FixW.fix_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:03:18.521345+00:00
-- url     : https://prove2.me/submissions/b871e5fe-51ac-4fd3-b724-9eb90a3ce58d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_FixSub
import Theorems.Thm_PI_StabSplit_FixW_mulVec_bvec

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
theorem _root_.solution {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ FixSet k r z)
    (j : Fin (2 * r + k + 1)) (hj : j.val < r) (i : Fin (2 * r + k + 1)) :
    g i j = if i = j then 1 else 0 := by
  have h := congrFun (hg.2 ⟨j.val, by omega⟩) i
  have e : eI k r ⟨j.val, hj⟩ = j := Fin.ext rfl
  simp only [fvec, dif_pos hj, e, mulVec_bvec] at h
  rw [h]; simp [bvec, Pi.single_apply]
end PI.StabSplit.FixW
