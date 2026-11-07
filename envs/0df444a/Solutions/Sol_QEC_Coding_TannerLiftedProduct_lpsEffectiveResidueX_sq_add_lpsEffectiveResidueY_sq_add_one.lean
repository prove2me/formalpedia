-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveResidueX_sq_add_lpsEffectiveResidueY_sq_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:41:44.686942+00:00
-- url     : https://prove2.me/submissions/5d55c0d3-8bd7-4795-9985-af2a9be182ce

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Find
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResidueCoordinates

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (q : ℕ) [Fact q.Prime] :
    lpsEffectiveResidueX q ^ 2 + lpsEffectiveResidueY q ^ 2 + 1 = 0 :=
  (Nat.find_spec (exists_lpsResiduePairCandidate q)).2
end QEC.Coding.TannerLiftedProduct
