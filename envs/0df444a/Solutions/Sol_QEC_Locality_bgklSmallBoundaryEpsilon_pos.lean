-- Prove2me | solution 1 for QEC.Locality.bgklSmallBoundaryEpsilon_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:33:52.285255+00:00
-- url     : https://prove2.me/submissions/4b06ae23-51dd-4dc0-afd2-92dac2e17d1d

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Theorems.Thm_QEC_Locality_bgklDecayRatio_lt_one

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution {beta exponent : ℝ}
    (hbeta : 1 ≤ beta) (hexponent : 0 < exponent) :
    0 < bgklSmallBoundaryEpsilon beta exponent := by
  have hratio := bgklDecayRatio_lt_one hexponent
  exact div_pos (sub_pos.mpr hratio) (mul_pos (by norm_num) (zero_lt_one.trans_le hbeta))
end QEC.Locality
