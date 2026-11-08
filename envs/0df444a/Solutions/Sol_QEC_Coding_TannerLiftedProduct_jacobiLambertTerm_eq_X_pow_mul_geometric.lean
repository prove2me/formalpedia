-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiLambertTerm_eq_X_pow_mul_geometric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:35:57.664955+00:00
-- url     : https://prove2.me/submissions/4c8d3027-f8a9-42fe-b965-442190dbb416

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiGeometricSeries_subst_mul_one_sub_X_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiLambertTerm_eq_geometric


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {d : ℕ} (hd : d ≠ 0) :
    jacobiLambertTerm d =
      PowerSeries.C (d : ℚ) * PowerSeries.X ^ d *
        jacobiGeometricSeries.subst (PowerSeries.X ^ d) := by
  rw [jacobiLambertTerm_eq_geometric hd]
  have hinv :
      jacobiGeometricSeries.subst
          ((PowerSeries.X : PowerSeries ℚ) ^ d) *
        (1 - (PowerSeries.X : PowerSeries ℚ) ^ d) = 1 :=
    jacobiGeometricSeries_subst_mul_one_sub_X_pow hd
  have htail :
      jacobiGeometricSeries.subst
          ((PowerSeries.X : PowerSeries ℚ) ^ d) - 1 =
        (PowerSeries.X : PowerSeries ℚ) ^ d *
          jacobiGeometricSeries.subst
            ((PowerSeries.X : PowerSeries ℚ) ^ d) := by
    linear_combination hinv
  rw [htail]
  ring
end QEC.Coding.TannerLiftedProduct
