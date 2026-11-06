-- Prove2me | solution 1 for QEC.Locality.BKQLDPCFamily.rpow_cN_eq_measuredSeparationProfile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:13:19.331573+00:00
-- url     : https://prove2.me/submissions/c989e232-202a-426c-96e2-7203e141c230

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
theorem _root_.solution
    (family : BKQLDPCFamily ι κ) (i : family.Index)
    {r : Nat} (hr : r ∈ family.validScales i) :
    Real.rpow (r : ℝ) (family.cN i r) =
      (family.measuredSeparationProfile i r : ℝ) := by
  have hrPos : (0 : ℝ) < r := by
    exact_mod_cast Nat.zero_lt_of_lt (family.one_lt_validScale i hr)
  have hrNeOne : (r : ℝ) ≠ 1 := by
    exact ne_of_gt (by exact_mod_cast family.one_lt_validScale i hr)
  have hprofilePos : (0 : ℝ) < family.measuredSeparationProfile i r := by
    exact_mod_cast family.measuredSeparationProfile_pos i hr
  exact Real.rpow_logb hrPos hrNeOne hprofilePos
end QEC.Locality.BKQLDPCFamily
