-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.lhol_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:14:39.431243+00:00
-- url     : https://prove2.me/submissions/0d4048ed-8558-46c7-9db6-13d3800430be

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsOfFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandHW
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhiA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {X : Matrix (Fin n) (Fin n) ℂ} {G H : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : Set.EqOn G H (OmegaSet n)) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    Lhol X G z = Lhol X H z := by
  show fderiv ℂ G z (X * z) = fderiv ℂ H z (X * z)
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (isOpen_OmegaSet'.mem_nhds hz) h)]
end ReciprocityTheory.ChartRestriction.DS.S7
