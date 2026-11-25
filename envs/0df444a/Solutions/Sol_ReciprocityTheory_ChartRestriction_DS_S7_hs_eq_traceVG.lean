-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.hs_eq_traceVG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:16:25.791034+00:00
-- url     : https://prove2.me/submissions/5bbafccf-4087-4133-a47b-488ff10baac8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (A : Matrix (Fin n) (Fin n) ℂ) : ((Aᴴ * A).trace).re = hs A := by
  have key : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := fun z => by
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm,
      Complex.normSq_apply]
    ring
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, hs,
    key]
  exact Finset.sum_comm
end ReciprocityTheory.ChartRestriction.DS.S7
