-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmStar.prod_signs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:42:50.288003+00:00
-- url     : https://prove2.me/submissions/3fe2272e-23b1-444f-b33f-dd23f4662550

import Definitions.Def_Formalism_PeriodIntegrals_QmStar
import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmStar
namespace PI.UnitaryGroupMassFormula.QmStar
theorem _root_.solution {n t : ℕ} (ε : Fin n → ℤˣ) (a b : Fin t → Fin n) (σ : Equiv.Perm (Fin t)) :
    (∏ k : Fin t, ((ε (a (σ k.rev)) * ε (b k.rev) : ℤˣ) : ℤ)) =
      (((∏ k, ε (a k)) * ∏ k, ε (b k) : ℤˣ) : ℤ) := by
  rw [← Units.coe_prod]
  congr 1
  rw [Finset.prod_mul_distrib]
  congr 1
  · exact Equiv.prod_comp (Fin.revPerm.trans σ) (fun k => ε (a k))
  · exact Equiv.prod_comp Fin.revPerm (fun k => ε (b k))
end PI.UnitaryGroupMassFormula.QmStar
