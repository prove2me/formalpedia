-- Prove2me | solution 1 for PI.BlockRatReal.UnitaryGroupMassFormula.eval_map_rowAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:59.530769+00:00
-- url     : https://prove2.me/submissions/f588e818-ec48-430a-974c-94476e1ab8ee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BlockRatReal
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylLeDual
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylMap
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylRowStable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_Bridge
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.BlockRatReal PI.BlockRatReal.UnitaryGroupMassFormula
namespace PI.BlockRatReal.UnitaryGroupMassFormula
theorem _root_.solution {LL : Type} [Field LL] (φ : LL →+* ℂ) {k : ℕ} (g : Matrix (Fin k) (Fin k) LL)
    (F : MvPolynomial (Fin k × Fin k) LL) (z : Matrix (Fin k) (Fin k) ℂ) :
    eval (fun x => z x.1 x.2) (MvPolynomial.map φ (Formalism.GradedWeylDivisibility.rowAct LL g F)) =
      eval (fun x => (g.map φ * z) x.1 x.2) (MvPolynomial.map φ F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [Formalism.GradedWeylDivisibility.rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    congr 1
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]
end PI.BlockRatReal.UnitaryGroupMassFormula
