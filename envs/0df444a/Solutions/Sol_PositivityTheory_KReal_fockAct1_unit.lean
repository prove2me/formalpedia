-- Prove2me | solution 1 for PositivityTheory.KReal.fockAct1_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:46:32.722014+00:00
-- url     : https://prove2.me/submissions/744b2b6a-f9a0-4c86-a651-a3ee799c9802

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Theorems.Thm_FockRL_fockAct1_eq
import Theorems.Thm_PI_FHS_fockAct1_eq
import Theorems.Thm_PI_FHS_omAct_apply
import Theorems.Thm_PI_WFJM_fockAct1_eq


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
variable {p q r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution (a b : Ix p q) (P : Pol p q r s) :
    fockAct1 p q r s (Eab a b) P = ∑ c : Ix r s, omE ((a, c) : Ln p q r s) (b, c) P := by
  rw [PI.FHS.fockAct1_eq, PI.FHS.omAct_apply]
  simp only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Eab, Matrix.single_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single a (by intro x _ hx; simp [Ne.symm hx]) (by simp)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_eq_single b (by intro x _ hx; simp [Ne.symm hx]) (by simp)]
  simp
end PositivityTheory.KReal
