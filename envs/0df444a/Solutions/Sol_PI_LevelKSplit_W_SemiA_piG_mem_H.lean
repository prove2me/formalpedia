-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiA.piG_mem_H
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:43:30.111851+00:00
-- url     : https://prove2.me/submissions/542817d8-4714-4718-b96b-eddc240a6aaf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulInvPiGMemN
import Theorems.Thm_Formalism_L2_SG_Sub_mem_stabT
import Theorems.Thm_PI_LevelKSplit_W_SemiA_datR_hyp
import Theorems.Thm_PI_LevelKSplit_W_SemiA_lin_piG
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_Pi_e
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_Pi_f
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_unipotent_proj_fixes_normal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
  (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP
namespace PI.LevelKSplit.W.SemiA
theorem _root_.solution (g : HA R σ J) (hg : g ∈ Ssub R σ J P) : piG hσσ hJ hP g hg ∈ Hsub R σ J P := by
  have H := datR_hyp (R := R) hσσ hJ hP
  unfold Hsub
  rw [mem_stabT]
  intro b
  rw [lin_piG]
  refine Fin.addCases (fun b => ?_) (fun b => ?_) b
  · rw [tupH, Fin.append_left]
    refine Fin.lastCases ?_ (fun a => ?_) b
    · rw [F0, Fin.snoc_last]
      exact SemiG.Dat.unipotent_proj_fixes_normal H _
    · rw [F0, Fin.snoc_castSucc]
      exact SemiG.Dat.Pi_e H _ a
  · rw [tupH, Fin.append_right]
    exact SemiG.Dat.Pi_f H _ b
end PI.LevelKSplit.W.SemiA
