-- Prove2me | solution 1 for PI.IsoDerivBFintype.eval_mY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:43:19.740075+00:00
-- url     : https://prove2.me/submissions/e1ac51ee-060f-46e3-b303-f3d103fdbf49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDerivB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ApplyAt0EqSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.IsoDerivBFintype
open PI.IsoDerivB
variable {Lt T : Type} [Fintype Lt] [DecidableEq Lt] (tp : Lt → T) {N N' : ℕ}
  (nu : Lt → YoungDiagram)
namespace PI.IsoDerivBFintype
theorem _root_.solution (J : ColChoice N nu) (y : T → Matrix (Fin N) (Fin N) ℂ) :
    MvPolynomial.eval (fun k : FrV T N => y k.1 k.2.1 k.2.2) (mY tp nu J) = minY N nu J (frC tp y) := by
  unfold mY minY
  rw [map_prod]
  refine prod_congr rfl fun z _ => ?_
  rw [map_prod]
  refine prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, frC, colsOf]
  split_ifs <;> simp
end PI.IsoDerivBFintype
