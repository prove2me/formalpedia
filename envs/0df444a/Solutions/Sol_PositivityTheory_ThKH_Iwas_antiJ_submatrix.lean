-- Prove2me | solution 1 for PositivityTheory.ThKH.Iwas.antiJ_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:01:12.625242+00:00
-- url     : https://prove2.me/submissions/cd2e651e-0917-4309-8e03-4b14d5c16112

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BigCellLocal
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_IwasLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Iwas
open Matrix Formalism.UG Formalism.UG.P GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
namespace PositivityTheory.ThKH.Iwas
theorem _root_.solution (L : Type) [Field L] (m : ℕ) :
    (antiJ L (m + m)).submatrix (ee m) (ee m) = Wm L (Fin m) := by
  ext (i | i) (j | j)
  · have := i.2; have := j.2
    simp only [submatrix_apply, antiJ, ee, Wm, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply,
      finSumFinEquiv_apply_left, Fin.val_castAdd, fromBlocks_apply₁₁, Matrix.zero_apply]
    rw [if_neg (by omega)]
  · have := i.2; have := j.2
    simp only [submatrix_apply, antiJ, ee, Wm, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      Equiv.refl_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd,
      fromBlocks_apply₁₂, Matrix.one_apply, Fin.revPerm_apply, Fin.val_rev, Fin.ext_iff]
    exact if_congr (by omega) rfl rfl
  · have := i.2; have := j.2
    simp only [submatrix_apply, antiJ, ee, Wm, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      Equiv.refl_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd,
      fromBlocks_apply₂₁, Matrix.one_apply, Fin.revPerm_apply, Fin.val_rev, Fin.ext_iff]
    exact if_congr (by omega) rfl rfl
  · have := i.2; have := j.2
    simp only [submatrix_apply, antiJ, ee, Wm, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
      finSumFinEquiv_apply_right, Fin.val_natAdd, fromBlocks_apply₂₂, Matrix.zero_apply, Fin.revPerm_apply, Fin.val_rev]
    rw [if_neg (by omega)]
end PositivityTheory.ThKH.Iwas
