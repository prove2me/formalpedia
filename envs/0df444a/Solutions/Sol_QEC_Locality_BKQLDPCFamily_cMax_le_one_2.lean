-- Prove2me | solution 2 for QEC.Locality.BKQLDPCFamily.cMax_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:12:51.505505+00:00
-- url     : https://prove2.me/submissions/b8d59213-2acf-4781-8da8-2ceb286d7af4

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_exists_validScale_cN_eq_cMax
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_cN_le_one

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
open QEC.Locality.BKQLDPCFamily
variable {ι : Nat → Type u} {κ : Nat → Type v}
variable [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Fintype (κ n)]
namespace QEC.Locality.BKQLDPCFamily
theorem _root_.solution (family : BKQLDPCFamily ι κ) (i : family.Index) :
    family.cMax i ≤ 1 := by
  rcases family.exists_validScale_cN_eq_cMax i with ⟨r, hr, hvalue⟩
  rw [← hvalue]
  exact family.cN_le_one i hr
end QEC.Locality.BKQLDPCFamily
