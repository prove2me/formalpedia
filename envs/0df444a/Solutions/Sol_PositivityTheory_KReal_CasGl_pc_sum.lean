-- Prove2me | solution 1 for PositivityTheory.KReal.CasGl.pc_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:06:37.742499+00:00
-- url     : https://prove2.me/submissions/6d547133-f9e7-4be9-bb04-6e62a60883d4

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCas
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasGl
import Theorems.Thm_PositivityTheory_KReal_CasGl_sum_sub

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
open PositivityTheory.KReal.CasGl
variable {r s : ℕ}
namespace PositivityTheory.KReal.CasGl
theorem _root_.solution {Z : Mat r s} (hZ : IsPC Z) : ∑ j : PIx r s, Z j.1.1 j.1.2 • Eab j.1.1 j.1.2 = Z := by
  rw [sum_sub (fun a b => ¬ sameBlock a b) (fun a b => Z a b • (Eab a b : Mat r s))]
  conv_rhs => rw [Matrix.matrix_eq_sum_single Z]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : sameBlock a b
  · simp [h, hZ a b h]
  · simp [h, Eab, Matrix.smul_single]
end PositivityTheory.KReal.CasGl
