-- Prove2me | solution 1 for PositivityTheory.KReal.omE_adj_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:26:13.451142+00:00
-- url     : https://prove2.me/submissions/7a058dbd-5a3e-4d78-8bcd-e75698c624a1

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Theorems.Thm_PositivityTheory_KReal_rai_adj
import Theorems.Thm_PositivityTheory_KReal_low_adj
import Theorems.Thm_FockRaiseLowInner_fockInner_add_left
import Theorems.Thm_FockRaiseLowInner_fockInner_add_right
import Theorems.Thm_FockRaiseLowInner_fockInner_smul_left
import Theorems.Thm_FockRaiseLowInner_fockInner_smul_right
import Theorems.Thm_FockRaiseLowInner_fockInner_zero_left
import Theorems.Thm_FockRaiseLowInner_fockInner_zero_right
import Theorems.Thm_PI_FHS_fockInner_add_left
import Theorems.Thm_PI_FHS_fockInner_add_right
import Theorems.Thm_PI_FHS_fockInner_smul_left
import Theorems.Thm_PI_FHS_fockInner_smul_right
import Theorems.Thm_PI_FHS_fockInner_zero_left
import Theorems.Thm_PI_FHS_fockInner_zero_right


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
theorem _root_.solution (l l' : Ln p q r s) (P Q : Pol p q r s) :
    fockInner (omE l l' P) Q = (sgnC l * sgnC l') * fockInner P (omE l' l Q) := by
  unfold omE
  simp only [LinearMap.add_apply, Module.End.mul_apply]
  rw [PI.FHS.fockInner_add_left, PI.FHS.fockInner_add_right, rai_adj, low_adj, mul_add, mul_assoc]
  congr 1
  by_cases h : l = l'
  · subst h
    have hs : sgnC l * sgnC l = 1 := by
      unfold sgnC; split_ifs <;> simp
    rw [hs, one_mul, if_pos rfl]
    simp only [LinearMap.smul_apply, Module.End.one_apply]
    rw [PI.FHS.fockInner_smul_left, PI.FHS.fockInner_smul_right]
    congr 1
    simp [map_ofNat]
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp only [LinearMap.zero_apply]
    rw [PI.FHS.fockInner_zero_left, PI.FHS.fockInner_zero_right, mul_zero]
end PositivityTheory.KReal
