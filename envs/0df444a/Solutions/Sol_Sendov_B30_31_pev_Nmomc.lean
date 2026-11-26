-- Prove2me | solution 1 for Sendov.B30_31.pev_Nmomc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:30:50.352218+00:00
-- url     : https://prove2.me/submissions/87ef04f5-b83d-4e72-bcc8-bd4a12046b64

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree30_31
import Theorems.Thm_Sendov_gg0_length
import Theorems.Thm_Sendov_gg1_length
import Theorems.Thm_Sendov_gg2_length
import Theorems.Thm_Sendov_l1_cons
import Theorems.Thm_Sendov_l1_nil
import Theorems.Thm_Sendov_l1row_cons
import Theorems.Thm_Sendov_l1row_nil
import Theorems.Thm_Sendov_npev_cons
import Theorems.Thm_Sendov_npev_nil
import Theorems.Thm_Sendov_pevZ_cons
import Theorems.Thm_Sendov_pevZ_nil
import Theorems.Thm_Sendov_pev_cons
import Theorems.Thm_Sendov_pev_nil
import Theorems.Thm_Sendov_pev_wsum_eq_of_packed
import Theorems.Thm_Sendov_qrow_entry_length_le
import Theorems.Thm_Sendov_qrow_length
import Theorems.Thm_Sendov_rev_cons
import Theorems.Thm_Sendov_rev_nil
import Theorems.Thm_Sendov_rowZ_bound
import Theorems.Thm_Sendov_rowZ_cons
import Theorems.Thm_Sendov_rowZ_length
import Theorems.Thm_Sendov_rowZ_nil
import Theorems.Thm_Sendov_rscale_length
import Theorems.Thm_Sendov_unpackN_succ
import Theorems.Thm_Sendov_unpackN_zero
import Theorems.Thm_Sendov_unpackZ_succ
import Theorems.Thm_Sendov_unpackZ_zero
import Theorems.Thm_Sendov_wsumZ_cons
import Theorems.Thm_Sendov_wsumZ_nil
import Theorems.Thm_Sendov_wsum_bound
import Theorems.Thm_Sendov_wsum_cons
import Theorems.Thm_Sendov_wsum_length_le
import Theorems.Thm_Sendov_wsum_nil
attribute [local simp] Sendov.gg0_length
attribute [local simp] Sendov.gg1_length
attribute [local simp] Sendov.gg2_length
attribute [local simp] Sendov.l1_cons
attribute [local simp] Sendov.l1_nil
attribute [local simp] Sendov.l1row_cons
attribute [local simp] Sendov.l1row_nil
attribute [local simp] Sendov.npev_cons
attribute [local simp] Sendov.npev_nil
attribute [local simp] Sendov.pevZ_cons
attribute [local simp] Sendov.pevZ_nil
attribute [local simp] Sendov.pev_cons
attribute [local simp] Sendov.pev_nil
attribute [local simp] Sendov.qrow_length
attribute [local simp] Sendov.rev_cons
attribute [local simp] Sendov.rev_nil
attribute [local simp] Sendov.rowZ_cons
attribute [local simp] Sendov.rowZ_length
attribute [local simp] Sendov.rowZ_nil
attribute [local simp] Sendov.rscale_length
attribute [local simp] Sendov.unpackN_succ
attribute [local simp] Sendov.unpackN_zero
attribute [local simp] Sendov.unpackZ_succ
attribute [local simp] Sendov.unpackZ_zero
attribute [local simp] Sendov.wsumZ_cons
attribute [local simp] Sendov.wsumZ_nil
attribute [local simp] Sendov.wsum_cons
attribute [local simp] Sendov.wsum_nil



set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B30_31
namespace Sendov.B30_31
theorem _root_.solution (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 30) (gg1 30) (gg2 30) 13)) α := by
  refine pev_wsum_eq_of_packed (gg0 30) (gg1 30) (gg2 30) 13 40 Lc betac
    tauc Nmomc (by norm_num [betac]) (by norm_num [tauc]) ?_ ?_ ?_ ?_ ?_ ?_ α
  · refine rowZ_bound (gg0 30) (gg1 30) (gg2 30) 13 3 betac tauc
      (by norm_num [betac]) (by simp) (by simp) (by simp) ?_
    norm_num [gg0, gg1, gg2, l1, betac, tauc]
  · decide
  · refine wsum_bound (gg0 30) (gg1 30) (gg2 30) 13 Lc betac
      (by norm_num [Lc]) ?_
    norm_num [gg0, gg1, gg2, l1, Lc, betac]
  · decide
  · exact wsum_length_le Lc _ 0
      (qrow_entry_length_le (gg0 30) (gg1 30) (gg2 30) 3 (by simp) (by simp) (by simp) 13)
  · rfl
end Sendov.B30_31
