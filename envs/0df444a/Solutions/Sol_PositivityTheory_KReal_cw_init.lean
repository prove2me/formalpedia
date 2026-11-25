-- Prove2me | solution 1 for PositivityTheory.KReal.cw_init
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:27:14.419926+00:00
-- url     : https://prove2.me/submissions/a7230edd-2f36-40a6-87e7-4fe125f6e71c

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution {r p : ℕ} (hp : p ≤ r) (c : ℚ) :
    ∑ k : Fin r, (if (k : ℕ) < p then c else 0) = p * c := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < p then c else 0) r, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have e : (Finset.range r).filter (fun k => k < p) = Finset.range p := by
    ext k
    simp
    omega
  rw [e, Finset.card_range]
end PositivityTheory.KReal
