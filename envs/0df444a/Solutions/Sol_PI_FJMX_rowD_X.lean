-- Prove2me | solution 1 for PI.FJMX.rowD_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:49.311158+00:00
-- url     : https://prove2.me/submissions/9b1d46a6-3d38-4625-915b-2808fe8cddbe

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
theorem _root_.solution (ι : Fin m × Fin n → σ) (hι : Function.Injective ι) (a b i : Fin m) (j : Fin n) :
    rowD ι a b (X (ι (i, j))) = if i = b then X (ι (a, j)) else 0 := by
  classical
  rw [rowD, derSum_apply, Finset.sum_eq_single j]
  · by_cases h : i = b
    · subst h; simp
    · have : ι (i, j) ≠ ι (b, j) := fun e => h (by have := hι e; simp at this; exact this)
      simp [h, pderiv_X_of_ne this]
  · intro k _ hk
    have : ι (i, j) ≠ ι (b, k) := fun e => hk (by have := hι e; simp at this; exact this.2.symm)
    simp [pderiv_X_of_ne this]
  · simp
end PI.FJMX
