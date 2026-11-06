-- Prove2me | solution 1 for QEC.Locality.profileDivisionPotentialCoefficient_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:41:38.95308+00:00
-- url     : https://prove2.me/submissions/31cfe10b-d53a-4ec1-a539-e43e12fd741d

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_DivisionPotential
section
noncomputable section
namespace QEC.Locality
private theorem profileDivisionRpowGap_pos
    {exponent : ℝ} (hexponent : 0 < exponent ∧ exponent < 1) :
    0 < profileDivisionRpowGap exponent := by
  have hquarter : (1 / 4 : ℝ) < (1 / 4 : ℝ) ^ exponent :=
    Real.self_lt_rpow_of_lt_one (by norm_num) (by norm_num) hexponent.2
  have hthreeQuarter : (3 / 4 : ℝ) < (3 / 4 : ℝ) ^ exponent :=
    Real.self_lt_rpow_of_lt_one (by norm_num) (by norm_num) hexponent.2
  unfold profileDivisionRpowGap
  linarith
end QEC.Locality
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
namespace QEC.Locality
theorem _root_.solution
    {beta exponent : ℝ} (hbeta : 1 ≤ beta)
    (hexponent : 0 < exponent ∧ exponent < 1) :
    0 < profileDivisionPotentialCoefficient beta exponent := by
  exact div_pos (mul_pos (by norm_num) (zero_lt_one.trans_le hbeta))
    (profileDivisionRpowGap_pos hexponent)
end QEC.Locality
