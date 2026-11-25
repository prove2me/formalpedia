-- Prove2me | solution 1 for PI.FJMX.shapeProd_hwb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:08:15.985254+00:00
-- url     : https://prove2.me/submissions/725a2e6c-a73a-4dc7-9f00-0ff73adc599e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LeadTDerCols
import Theorems.Thm_P2M_PI_FJMX_leadT_der_rows__f69cea871e0f
import Theorems.Thm_P2M_PI_FJMX_leadT_der_cols__97589a762974
import Theorems.Thm_P2M_PI_FJMX_shapeProd_der__29b51981dd02
import Theorems.Thm_PI_FJMX_bRow_eq_rowD
import Theorems.Thm_PI_FJMX_bCol_eq_colD
import Theorems.Thm_PI_FJMX_rowD_X
import Theorems.Thm_PI_FJMX_colD_X

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
theorem _root_.solution (ι : Fin m × Fin n → σ) (hι : Function.Injective ι) (α : List ℕ) :
    PI.FJMB.HWB ι (PI.FJM.shapeProd (blkM ι) α) := by
  refine ⟨fun a b hab => ?_, fun c d hcd => ?_⟩
  · rw [bRow_eq_rowD]
    apply shapeProd_der'
    intro t
    apply leadT_der_rows'
    intro i₀ hi₀
    by_cases hb : i₀ = b
    · right
      subst hb
      refine ⟨a, by omega, ne_of_lt hab, 1, fun j _ => ?_⟩
      simp [blkM, rowD_X ι hι]
    · left
      intro j _
      simp [blkM, rowD_X ι hι, hb]
  · rw [bCol_eq_colD]
    apply shapeProd_der'
    intro t
    apply leadT_der_cols'
    intro j₀ hj₀
    by_cases hd : j₀ = d
    · right
      subst hd
      refine ⟨c, by omega, ne_of_lt hcd, 1, fun i _ => ?_⟩
      simp [blkM, colD_X ι hι]
    · left
      intro i _
      simp [blkM, colD_X ι hι, hd]
end PI.FJMX
