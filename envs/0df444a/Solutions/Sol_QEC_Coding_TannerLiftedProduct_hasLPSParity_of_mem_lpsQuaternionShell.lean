-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.hasLPSParity_of_mem_lpsQuaternionShell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:02:06.486935+00:00
-- url     : https://prove2.me/submissions/32504d50-9e56-47be-9b31-54c390bc2559

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) {t : LPSQuaternion}
    (ht : t ∈ lpsQuaternionShell p) : t.HasLPSParity := by
  have hnorm := norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos ht
  have hnormalized :=
    (mem_lpsQuaternionShell_iff a.degreePrime.pos t).mp ht
  have hodd := exactly_one_odd_coordinate a.degreeModFour t hnorm
  rcases hodd with hfirst | hsecond | hthird | hfourth
  · exact ⟨hnormalized.2.2,
      Int.not_odd_iff_even.mp hfirst.2.1,
      Int.not_odd_iff_even.mp hfirst.2.2.1,
      Int.not_odd_iff_even.mp hfirst.2.2.2⟩
  · exact (hsecond.1 hnormalized.2.2).elim
  · exact (hthird.1 hnormalized.2.2).elim
  · exact (hfourth.1 hnormalized.2.2).elim
end QEC.Coding.TannerLiftedProduct
