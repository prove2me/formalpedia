-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.hasLPSParity_of_mem_lpsQuaternionShell_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:46:17.523082+00:00
-- url     : https://prove2.me/submissions/57666c58-6f53-49af-8685-68826b4a67cf

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Matrix
open scoped LinearAlgebra.Projectivization
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hp4 : p % 4 = 1) {t : LPSQuaternion}
    (ht : t ∈ lpsQuaternionShell p) : t.HasLPSParity := by
  have hpPos : 0 < p := by
    by_contra h
    interval_cases p <;> norm_num at hp4
  have hnorm := norm_eq_of_mem_lpsQuaternionShell hpPos ht
  have hnormalized := (mem_lpsQuaternionShell_iff hpPos t).mp ht
  rcases exactly_one_odd_coordinate hp4 t hnorm with
      hfirst | hsecond | hthird | hfourth
  · exact ⟨hnormalized.2.2,
      Int.not_odd_iff_even.mp hfirst.2.1,
      Int.not_odd_iff_even.mp hfirst.2.2.1,
      Int.not_odd_iff_even.mp hfirst.2.2.2⟩
  · exact (hsecond.1 hnormalized.2.2).elim
  · exact (hthird.1 hnormalized.2.2).elim
  · exact (hfourth.1 hnormalized.2.2).elim
end QEC.Coding.TannerLiftedProduct
