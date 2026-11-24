-- Prove2me | solution 1 for PI.FockOneDegW.Core.pd_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:16.719645+00:00
-- url     : https://prove2.me/submissions/967d15a6-db0c-4568-a911-aa66e8140e4e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.Core
open PI.FockOneDegW PI.FockOneDegW.Inner PI.FockOneDegW.Diag
namespace PI.FockOneDegW.Core
theorem _root_.solution {σ : Type*} (i j : σ) (P : MvPolynomial σ ℂ) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    have hc : ∀ a b : σ, pderiv a (pderiv b (X n : MvPolynomial σ ℂ)) = 0 := by
      intro a b
      rw [pderiv_X, Pi.single_apply]
      split_ifs
      · exact Derivation.map_one_eq_zero _
      · exact map_zero _
    simp only [Derivation.leibniz, map_add, smul_eq_mul]
    rw [hc i j, hc j i, hp]
    ring
end PI.FockOneDegW.Core
