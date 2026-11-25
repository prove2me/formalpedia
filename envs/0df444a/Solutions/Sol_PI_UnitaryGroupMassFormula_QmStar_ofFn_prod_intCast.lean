-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmStar.ofFn_prod_intCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:42:34.206149+00:00
-- url     : https://prove2.me/submissions/f8131208-e1f0-450d-8f12-f2c42f5dcabf

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
theorem _root_.solution {A : Type*} [Ring A] : ∀ {t : ℕ} (s : Fin t → ℤ) (g : Fin t → A),
    (List.ofFn fun k => (s k : A) * g k).prod = ((∏ k, s k : ℤ) : A) * (List.ofFn g).prod
  | 0, s, g => by simp
  | t + 1, s, g => by
    have ih := solution (fun k => s k.succ) (fun k => g k.succ)
    rw [List.ofFn_succ, List.prod_cons, ih, List.ofFn_succ (f := g), List.prod_cons,
      Fin.prod_univ_succ, Int.cast_mul]
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc, ← mul_assoc, Int.cast_comm]
end PI.UnitaryGroupMassFormula.QmStar
