-- Prove2me | solution 1 for PositivityTheory.KReal.fockAct2_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:32:07.180096+00:00
-- url     : https://prove2.me/submissions/a237aaa5-35ca-4b03-a277-fcea949eb04d

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Theorems.Thm_FockRL_fockAct2_eq
import Theorems.Thm_PI_FHS_fockAct2_eq
import Theorems.Thm_PI_FHS_omAct_apply
import Theorems.Thm_PI_WFJM_fockAct2_eq


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
theorem _root_.solution (c d : Ix r s) (P : Pol p q r s) :
    fockAct2 p q r s (Eab c d) P = ∑ a : Ix p q, omE ((a, c) : Ln p q r s) (a, d) P := by
  rw [PI.FHS.fockAct2_eq, PI.FHS.omAct_apply]
  simp only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Eab, Matrix.single_apply, Matrix.one_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single c (by intro x _ hx; simp [Ne.symm hx]) (by simp)]
  rw [Finset.sum_eq_single a (by intro x _ hx; simp [Ne.symm hx]) (by simp)]
  rw [Finset.sum_eq_single d (by intro x _ hx; simp [Ne.symm hx]) (by simp)]
  simp
end PositivityTheory.KReal
