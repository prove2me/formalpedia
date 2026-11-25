-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmStar.star_ofFn_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:42:58.613183+00:00
-- url     : https://prove2.me/submissions/5afe3fa7-3aa1-447b-9caa-d3230558084d

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
theorem _root_.solution {A : Type*} [Ring A] [StarRing A] : ∀ {t : ℕ} (f : Fin t → A),
    star (List.ofFn f).prod = (List.ofFn fun i => star (f i.rev)).prod
  | 0, f => by simp
  | t + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, star_mul, solution (fun i => f i.succ),
      List.ofFn_succ' (fun i : Fin (t + 1) => star (f i.rev)), List.prod_concat]
    simp only [Fin.rev_last, Fin.rev_castSucc]
end PI.UnitaryGroupMassFormula.QmStar
