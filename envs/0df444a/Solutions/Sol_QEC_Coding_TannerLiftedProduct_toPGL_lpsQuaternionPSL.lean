-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.toPGL_lpsQuaternionPSL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:33:10.05132+00:00
-- url     : https://prove2.me/submissions/53c7b901-8f4b-4359-9c57-683e72152b20

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResiduePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResidueCoordinates
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Matrix
open QEC.Coding.BalancedProduct.LPSArithmetic
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL
        (lpsQuaternionPSL a t ht) = lpsQuaternionPGL a t ht :=
  Classical.choose_spec (lpsQuaternionPGL_mem_range_toPGL a t ht)
end QEC.Coding.TannerLiftedProduct
