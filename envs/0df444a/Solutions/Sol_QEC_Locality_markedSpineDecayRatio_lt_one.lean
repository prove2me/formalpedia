-- Prove2me | solution 1 for QEC.Locality.markedSpineDecayRatio_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:16:50.963792+00:00
-- url     : https://prove2.me/submissions/55473e83-ea67-480b-87c5-0e6dd3c38319

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted

set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution {exponent : ℝ} (hexponent : 0 < exponent) :
    markedSpineDecayRatio exponent < 1 := by
  rw [markedSpineDecayRatio, ← Real.one_rpow exponent]
  exact Real.rpow_lt_rpow (by norm_num) (by norm_num) hexponent
end QEC.Locality
