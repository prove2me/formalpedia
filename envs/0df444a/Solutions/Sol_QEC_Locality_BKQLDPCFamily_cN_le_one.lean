-- Prove2me | solution 1 for QEC.Locality.BKQLDPCFamily.cN_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:13:09.842495+00:00
-- url     : https://prove2.me/submissions/02ba0d68-2165-41b8-a7d1-ccbab5fea9f7

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_one_lt_validScale
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_measuredSeparationProfile_pos
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_measuredSeparationProfile_le_scale

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
    family.cN i r ≤ 1 := by
  calc
    family.cN i r ≤ Real.logb (r : ℝ) (r : ℝ) := by
      apply Real.logb_le_logb_of_le
      · exact_mod_cast family.one_lt_validScale i hr
      · exact_mod_cast family.measuredSeparationProfile_pos i hr
      · exact_mod_cast family.measuredSeparationProfile_le_scale i r
    _ = 1 := Real.logb_self_eq_one (by
      exact_mod_cast family.one_lt_validScale i hr)
end QEC.Locality.BKQLDPCFamily
