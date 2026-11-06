-- Prove2me | solution 1 for QEC.Locality.BKQLDPCFamily.cMax_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:23:12.711923+00:00
-- url     : https://prove2.me/submissions/944a0dbc-f4f2-494b-abba-267ec3437293

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_exists_validScale_cN_eq_cMax
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_cN_lt_one

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
open QEC.Locality.BKQLDPCFamily
variable {ι : Nat → Type u} {κ : Nat → Type v}
variable [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Fintype (κ n)]
namespace QEC.Locality.BKQLDPCFamily
theorem _root_.solution (family : BKQLDPCFamily ι κ) (i : family.Index) :
    family.cMax i < 1 := by
  rcases family.exists_validScale_cN_eq_cMax i with ⟨r, hr, hvalue⟩
  rw [← hvalue]
  exact family.cN_lt_one i hr
end QEC.Locality.BKQLDPCFamily
