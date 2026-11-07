-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveResiduePairIndex_lt_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:41:38.529587+00:00
-- url     : https://prove2.me/submissions/28add6b1-003e-4a77-a2b2-2707fbc1e0a6

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Find
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResidueCoordinates

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] :
    lpsEffectiveResiduePairIndex q < q ^ 2 :=
  (Nat.find_spec (exists_lpsResiduePairCandidate q)).1
end QEC.Coding.TannerLiftedProduct
