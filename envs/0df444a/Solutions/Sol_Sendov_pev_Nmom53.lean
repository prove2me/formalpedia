-- Prove2me | solution 1 for Sendov.pev_Nmom53
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:19:24.171605+00:00
-- url     : https://prove2.me/submissions/f3b3d626-cb1b-4210-b749-38b2584abac8

import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree53Packed
import Theorems.Thm_Sendov_pev_wsum_eq_of_packed
import Theorems.Thm_Sendov_qrow_entry_length_le
import Theorems.Thm_Sendov_rowZ_bound
import Theorems.Thm_Sendov_wsum_bound
import Theorems.Thm_Sendov_wsum_length_le


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 1000000
open Sendov
namespace Sendov
theorem _root_.solution (α : ℝ) :
    pev Nmom53 α = pev (wsum L53 0 (qrow (gg0 53) (gg1 53) (gg2 53) 24)) α := by
  refine pev_wsum_eq_of_packed (gg0 53) (gg1 53) (gg2 53) 24 73 L53 beta53 tau53 Nmom53
    (by norm_num [beta53]) (by norm_num [tau53]) ?_ ?_ ?_ ?_ ?_ ?_ α
  · refine rowZ_bound (gg0 53) (gg1 53) (gg2 53) 24 3 beta53 tau53 (by norm_num [beta53])
      (by decide) (by decide) (by decide) ?_
    norm_num [gg0, gg1, gg2, l1, beta53, tau53]
  · decide
  · refine wsum_bound (gg0 53) (gg1 53) (gg2 53) 24 L53 beta53 (by norm_num [L53]) ?_
    norm_num [gg0, gg1, gg2, l1, L53, beta53]
  · decide
  · exact wsum_length_le L53 _ 0
      (qrow_entry_length_le (gg0 53) (gg1 53) (gg2 53) 3 (by decide) (by decide) (by decide) 24)
  · rfl
end Sendov
