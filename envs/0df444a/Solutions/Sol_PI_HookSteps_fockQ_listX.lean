-- Prove2me | solution 1 for PI.HookSteps.fockQ_listX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:45:19.766542+00:00
-- url     : https://prove2.me/submissions/14e20594-d0a3-48bb-a577-4f075d4dc9fb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DeterminantAdjugate
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
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
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookSteps
namespace PI.HookSteps
theorem _root_.solution (hX : MulXAdj) {σ : Type} (l : List σ) (f g : MvPolynomial σ ℚ) :
    fockQ ((l.map fun v => (X v : MvPolynomial σ ℚ)).prod * f) g =
      fockQ f ((l.map fun v => ((pderiv v : Derivation ℚ _ _).toLinearMap :
        Module.End ℚ (MvPolynomial σ ℚ))).prod g) := by
  induction l generalizing f g with
  | nil => simp
  | cons v l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [mul_assoc, mul_left_comm, ih, hX σ v]
    rfl
end PI.HookSteps
