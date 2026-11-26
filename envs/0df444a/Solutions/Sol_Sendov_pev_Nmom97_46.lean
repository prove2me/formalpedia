-- Prove2me | solution 1 for Sendov.pev_Nmom97_46
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:19:24.725811+00:00
-- url     : https://prove2.me/submissions/35bacd2c-149e-4add-bd6e-d4b7d1f5c052

import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree97Packed
import Theorems.Thm_Sendov_pev_wsum_eq_of_packed
import Theorems.Thm_Sendov_qrow_entry_length_le
import Theorems.Thm_Sendov_rowZ_bound
import Theorems.Thm_Sendov_wsum_bound
import Theorems.Thm_Sendov_wsum_length_le


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
namespace Sendov
theorem _root_.solution (α : ℝ) :
    pev Nmom97_46 α = pev (wsum L97_46 0 (qrow (gg0 97) (gg1 97) (gg2 97) 46)) α := by
  refine pev_wsum_eq_of_packed (gg0 97) (gg1 97) (gg2 97) 46 139 L97_46 beta97_46 tau97_46
    Nmom97_46 (by norm_num [beta97_46]) (by norm_num [tau97_46]) ?_ ?_ ?_ ?_ ?_ ?_ α
  · refine rowZ_bound (gg0 97) (gg1 97) (gg2 97) 46 3 beta97_46 tau97_46
      (by norm_num [beta97_46]) (by decide) (by decide) (by decide) ?_
    norm_num [gg0, gg1, gg2, l1, beta97_46, tau97_46]
  · decide
  · refine wsum_bound (gg0 97) (gg1 97) (gg2 97) 46 L97_46 beta97_46
      (by norm_num [L97_46]) ?_
    norm_num [gg0, gg1, gg2, l1, L97_46, beta97_46]
  · decide
  · exact wsum_length_le L97_46 _ 0
      (qrow_entry_length_le (gg0 97) (gg1 97) (gg2 97) 3 (by decide) (by decide) (by decide) 46)
  · rfl
end Sendov
