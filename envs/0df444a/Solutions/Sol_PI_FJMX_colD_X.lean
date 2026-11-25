-- Prove2me | solution 1 for PI.FJMX.colD_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:39:05.345244+00:00
-- url     : https://prove2.me/submissions/3112c6cf-c87e-485c-ad30-13560c13646b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LeadTDerCols
import Theorems.Thm_PI_FJMX_derSum_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMX
variable {σ : Type*} {m n : ℕ}
namespace PI.FJMX
theorem _root_.solution (ι : Fin m × Fin n → σ) (hι : Function.Injective ι) (c d : Fin n) (i : Fin m) (j : Fin n) :
    colD ι c d (X (ι (i, j))) = if j = d then X (ι (i, c)) else 0 := by
  classical
  rw [colD, derSum_apply, Finset.sum_eq_single i]
  · by_cases h : j = d
    · subst h; simp
    · have : ι (i, j) ≠ ι (i, d) := fun e => h (by have := hι e; simp at this; exact this)
      simp [h, pderiv_X_of_ne this]
  · intro k _ hk
    have : ι (i, j) ≠ ι (k, d) := fun e => hk (by have := hι e; simp at this; exact this.1.symm)
    simp [pderiv_X_of_ne this]
  · simp
end PI.FJMX
