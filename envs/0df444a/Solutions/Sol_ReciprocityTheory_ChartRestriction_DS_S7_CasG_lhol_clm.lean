-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CasG.lhol_clm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:01.097563+00:00
-- url     : https://prove2.me/submissions/177c23d7-905d-4906-842d-6d4e7942f18b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiMLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasLPsM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LholClmEventually

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.CasG
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace ReciprocityTheory.ChartRestriction.DS.S7.CasG
theorem _root_.solution (L : E →L[ℂ] E') (X : Matrix (Fin n) (Fin n) ℂ) {G : Matrix (Fin n) (Fin n) ℂ → E}
    {z : Matrix (Fin n) (Fin n) ℂ} (hG : DifferentiableAt ℂ G z) :
    Lhol X (fun w => L (G w)) z = L (Lhol X G z) := by
  unfold Lhol
  have h1 : (fun w => L (G w)) = L ∘ G := rfl
  rw [h1]
  have h2 := (L.hasFDerivAt.comp z hG.hasFDerivAt).fderiv
  exact congrArg (fun A : Matrix (Fin n) (Fin n) ℂ →L[ℂ] E' => A (X * z)) h2
end ReciprocityTheory.ChartRestriction.DS.S7.CasG
