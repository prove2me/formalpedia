-- Prove2me | solution 1 for SZ.sqrtThree_notMem_S
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:51.685997+00:00
-- url     : https://prove2.me/submissions/7c2eaa3d-9967-49ed-a4fc-b7238230140b

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
import Theorems.Thm_SZ_sqrtThree_mem_MahlerZ

set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution : Real.sqrt 3 ∉ S := fun h => h.2 sqrtThree_mem_MahlerZ
end SZ
