-- Prove2me | solution 1 for QEC.Locality.BKQLDPCFamily.measuredSeparationProfile_le_rpow_cMax
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:21:14.019027+00:00
-- url     : https://prove2.me/submissions/9ea9b5c9-f78f-41b5-9833-755546849427

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_one_lt_validScale
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_cN_le_cMax
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_rpow_cN_eq_measuredSeparationProfile

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
open QEC.Locality.BKQLDPCFamily
variable {ι : Nat → Type u} {κ : Nat → Type v}
variable [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Fintype (κ n)]
namespace QEC.Locality.BKQLDPCFamily
theorem _root_.solution
    (family : BKQLDPCFamily ι κ) (i : family.Index)
    {r : Nat} (hr : r ∈ family.validScales i) :
    (family.measuredSeparationProfile i r : ℝ) ≤
      Real.rpow (r : ℝ) (family.cMax i) := by
  rw [← family.rpow_cN_eq_measuredSeparationProfile i hr]
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast Nat.le_of_lt (family.one_lt_validScale i hr)
  · exact family.cN_le_cMax i hr
end QEC.Locality.BKQLDPCFamily
