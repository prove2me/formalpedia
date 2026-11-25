-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.M_inUJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:25:26.885795+00:00
-- url     : https://prove2.me/submissions/7e3d7f41-c105-4089-b6ab-0bee8fac9f93

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_M_unitary
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PI PI.ScPiBuildW PI.ScPiBuildW.Loc
open PI.ScPiExists
open PI.ScPiBuildW.Loc.LocFrame
variable {n r k : ℕ} {ε : Fin n → Bool} (L : LocFrame n r k ε)
namespace PI.ScPiBuildW.Loc.LocFrame
theorem _root_.solution {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hS : InS L.e L.z g) :
    L.M g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k) := by
  have hJ1 : PI.UpqRep.Jm (PI.UpqRep.allPos k) = 1 := by
    ext a b
    simp [PI.UpqRep.Jm, PI.UpqRep.allPos, Matrix.diagonal_apply, Matrix.one_apply]
  show (L.M g)ᴴ * PI.UpqRep.Jm (PI.UpqRep.allPos k) * L.M g = PI.UpqRep.Jm (PI.UpqRep.allPos k)
  rw [hJ1, Matrix.mul_one, L.M_unitary hg hS]
end PI.ScPiBuildW.Loc.LocFrame
