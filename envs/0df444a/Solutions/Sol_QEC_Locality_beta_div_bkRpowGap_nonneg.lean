-- Prove2me | solution 1 for QEC.Locality.beta_div_bkRpowGap_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:14:57.612285+00:00
-- url     : https://prove2.me/submissions/65b076c9-ce43-4ba8-8977-7685a9eb57d3

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Theorems.Thm_QEC_Locality_bkRpowGap_pos

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open Set
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    {beta c : ℝ} (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    0 ≤ beta / bkRpowGap c :=
  div_nonneg hbeta (bkRpowGap_pos hc0 hc1).le
end QEC.Locality
