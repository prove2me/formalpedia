-- Prove2me | solution 1 for PIQnLT.bvec_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:21:27.001515+00:00
-- url     : https://prove2.me/submissions/b435af27-216b-494a-9067-51891f1164b7

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_SecondCapelliMinorLevel
import Theorems.Thm_PIQnLT_lev_inj
import Theorems.Thm_PIQnLT_lev_val
import Theorems.Thm_PIQnLT_liftVec_lev
import Theorems.Thm_PIQnLT_liftVec_out


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PIQnLT
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k i r' : ℕ}
namespace PIQnLT
theorem _root_.solution (q : Fin (2 * r' + k + 1)) : bvec (levPos k i r' q) = liftVec k i r' (bvec q) := by
  funext p
  by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
  · obtain ⟨a, rfl⟩ : ∃ a, levPos k i r' a = p :=
      ⟨⟨p.val - i, by omega⟩, Fin.ext (by show p.val - i + i = p.val; omega)⟩
    rw [liftVec_lev]
    simp only [bvec, Pi.single_apply, lev_inj.eq_iff]
  · rw [liftVec_out _ _ hp]
    simp only [bvec, Pi.single_apply]
    rw [if_neg]
    rintro rfl
    apply hp
    rw [lev_val]
    have := q.isLt
    omega
end PIQnLT
