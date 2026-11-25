-- Prove2me | solution 1 for PositivityTheory.KReal.cw_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:24:04.529124+00:00
-- url     : https://prove2.me/submissions/b3d9d4c3-4af4-450b-a7ee-69393e0ade37

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
theorem _root_.solution {r q : ℕ} (hq : q ≤ r) (c : ℚ) :
    ∑ k : Fin r, (if r ≤ (k : ℕ) + q then c else 0) = q * c := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if r ≤ k + q then c else 0) r, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have e : (Finset.range r).filter (fun k => r ≤ k + q) = Finset.Ico (r - q) r := by
    ext k
    simp
    omega
  rw [e, Nat.card_Ico, show r - (r - q) = q by omega]
end PositivityTheory.KReal
