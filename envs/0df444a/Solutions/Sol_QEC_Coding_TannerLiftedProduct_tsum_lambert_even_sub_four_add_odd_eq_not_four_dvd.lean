-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.tsum_lambert_even_sub_four_add_odd_eq_not_four_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:59:31.299831+00:00
-- url     : https://prove2.me/submissions/1a99e9a7-8d3f-4ca6-84e4-72fe62c843f5

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_tsum_lambert_even_sub_four_add_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_tsum_lambert_not_four_dvd

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    (∑' n : ℕ,
        (jacobiLambertTerm (2 * (n + 1)) -
          jacobiLambertTerm (4 * (n + 1)) +
          jacobiLambertTerm (2 * n + 1))) =
      ∑' d : ℕ, if 4 ∣ d then 0 else jacobiLambertTerm d := by
  rw [tsum_lambert_even_sub_four_add_odd,
    tsum_lambert_not_four_dvd]
end QEC.Coding.TannerLiftedProduct
