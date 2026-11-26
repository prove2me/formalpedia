-- Prove2me | solution 1 for Sendov.wsum_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:13:03.14738+00:00
-- url     : https://prove2.me/submissions/47ee84cd-a5f8-431f-a3b3-3b438bc094f8

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
import Theorems.Thm_Sendov_l1row_nil
import Theorems.Thm_Sendov_l1row_cons
import Theorems.Thm_Sendov_padd_length
import Theorems.Thm_Sendov_rscale_length
import Theorems.Thm_Sendov_qrow_length
import Theorems.Thm_Sendov_wsumZ_nil
import Theorems.Thm_Sendov_wsumZ_cons
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
attribute [local simp] Sendov.l1row_nil
attribute [local simp] Sendov.l1row_cons
attribute [local simp] Sendov.rscale_length
attribute [local simp] Sendov.qrow_length
attribute [local simp] Sendov.wsumZ_nil
attribute [local simp] Sendov.wsumZ_cons

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution {m : ℕ} (L : ℤ) : ∀ (r : List (List ℤ)) (i : ℕ),
    (∀ p ∈ r, p.length ≤ m) → (wsum L i r).length ≤ m := by
  intro r
  induction r with
  | nil => intro i _; simp
  | cons p r ih =>
    intro i hr
    have hp := hr p (List.mem_cons_self ..)
    have := ih (i + 1) (fun q hq => hr q (List.mem_cons_of_mem _ hq))
    simp only [wsum_cons, padd_length, List.length_map]
    omega
end Sendov
