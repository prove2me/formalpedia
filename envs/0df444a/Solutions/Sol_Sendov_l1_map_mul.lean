-- Prove2me | solution 1 for Sendov.l1_map_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:04:00.431408+00:00
-- url     : https://prove2.me/submissions/0c676834-b17d-4ca2-9efc-72cb9431d559

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Theorems.Thm_Sendov_rowZ_nil
import Theorems.Thm_Sendov_rowZ_cons
import Theorems.Thm_Sendov_rowZ_length
import Theorems.Thm_Sendov_wsum_nil
import Theorems.Thm_Sendov_wsum_cons
import Theorems.Thm_Sendov_l1_nil
import Theorems.Thm_Sendov_l1_cons
import Theorems.Thm_Sendov_gg0_length
import Theorems.Thm_Sendov_gg1_length
import Theorems.Thm_Sendov_gg2_length
import Theorems.Thm_Sendov_npev_cons
import Theorems.Thm_Sendov_npev_nil
import Theorems.Thm_Sendov_pevZ_cons
import Theorems.Thm_Sendov_pevZ_nil
import Theorems.Thm_Sendov_pev_cons
import Theorems.Thm_Sendov_pev_nil
import Theorems.Thm_Sendov_rev_cons
import Theorems.Thm_Sendov_rev_nil
import Theorems.Thm_Sendov_unpackN_succ
import Theorems.Thm_Sendov_unpackN_zero
import Theorems.Thm_Sendov_unpackZ_succ
import Theorems.Thm_Sendov_unpackZ_zero
attribute [local simp] Sendov.gg0_length
attribute [local simp] Sendov.gg1_length
attribute [local simp] Sendov.gg2_length
attribute [local simp] Sendov.npev_cons
attribute [local simp] Sendov.npev_nil
attribute [local simp] Sendov.pevZ_cons
attribute [local simp] Sendov.pevZ_nil
attribute [local simp] Sendov.pev_cons
attribute [local simp] Sendov.pev_nil
attribute [local simp] Sendov.rev_cons
attribute [local simp] Sendov.rev_nil
attribute [local simp] Sendov.unpackN_succ
attribute [local simp] Sendov.unpackN_zero
attribute [local simp] Sendov.unpackZ_succ
attribute [local simp] Sendov.unpackZ_zero


attribute [local simp] Sendov.rowZ_nil
attribute [local simp] Sendov.rowZ_cons
attribute [local simp] Sendov.rowZ_length
attribute [local simp] Sendov.wsum_nil
attribute [local simp] Sendov.wsum_cons
attribute [local simp] Sendov.l1_nil
attribute [local simp] Sendov.l1_cons

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (c : ℤ) (q : List ℤ) : l1 (q.map (fun x => c * x)) = |c| * l1 q := by
  induction q with
  | nil => simp
  | cons b q ih =>
    simp only [List.map_cons, l1_cons, ih, abs_mul]
    ring
end Sendov
