-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.QRG.H_gm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:40:23.409137+00:00
-- url     : https://prove2.me/submissions/59851a18-a6ce-4869-8719-b8c76bb271d5

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_H_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.QRG
open Matrix Formalism.UG
variable {K : Type} [Field K] {n : ℕ}
variable (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)
namespace PI.UnitaryGroupMassFormula.AdIndexEq.QRG
theorem _root_.solution (g : UJ σ J) (x y : Fin n → K) : H σ J (gm σ J g *ᵥ x) (gm σ J g *ᵥ y) = H σ J x y := by exact H_of_mem σ J g.1 g.2 x y
end PI.UnitaryGroupMassFormula.AdIndexEq.QRG
