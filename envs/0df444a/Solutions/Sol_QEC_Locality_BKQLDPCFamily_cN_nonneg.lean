-- Prove2me | solution 1 for QEC.Locality.BKQLDPCFamily.cN_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:13:00.992565+00:00
-- url     : https://prove2.me/submissions/83a2ba57-5945-4f79-b7ba-d288d419ccf9

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_one_lt_validScale
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_measuredSeparationProfile_pos

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
open QEC.Locality.BKQLDPCFamily
variable {ι : Nat → Type u} {κ : Nat → Type v}
variable [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Fintype (κ n)]
namespace QEC.Locality.BKQLDPCFamily
theorem _root_.solution (family : BKQLDPCFamily ι κ)
    (i : family.Index) {r : Nat} (hr : r ∈ family.validScales i) :
    0 ≤ family.cN i r := by
  apply Real.logb_nonneg
  · exact_mod_cast family.one_lt_validScale i hr
  · exact_mod_cast Nat.succ_le_iff.mpr (family.measuredSeparationProfile_pos i hr)
end QEC.Locality.BKQLDPCFamily
