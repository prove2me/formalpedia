-- Prove2me | solution 1 for PositivityTheory.KReal.act_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:30:38.55804+00:00
-- url     : https://prove2.me/submissions/f2197b06-3710-4342-9309-fffda178f721

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc

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
variable {r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] (act : Mat r s →ₗ[ℂ] Module.End ℂ M) (W : Mat r s) :
    act W = ∑ a, ∑ b, W a b • act (Eab a b) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single W]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← map_smul, Eab, Matrix.smul_single, smul_eq_mul, mul_one]
end PositivityTheory.KReal
