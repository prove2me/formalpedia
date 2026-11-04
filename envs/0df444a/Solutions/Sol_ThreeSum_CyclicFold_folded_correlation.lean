-- Prove2me | solution 1 for ThreeSum.CyclicFold.folded_correlation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:12.148183+00:00
-- url     : https://prove2.me/submissions/e4258e68-2d05-447a-8c1f-a9e8246a989c

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_Submission_ThreeSum_CyclicFold
import Theorems.Thm_ThreeSum_CyclicFold_fold_product
import Theorems.Thm_ThreeSum_CyclicFold_vector_length
import Definitions.Def_WeightedCache3SUM_Alias_b64063ffc0d0e625

set_option autoImplicit false
open ThreeSum ThreeSum.CyclicFold
open Finset Polynomial Karatsuba
open scoped BigOperators
namespace ThreeSum.CyclicFold
theorem _root_.solution {p : ℕ} [NeZero p]
    (F H : ZMod p → ℕ) (r : ℕ) (hr : r < p) :
    (asPolynomial (vector p F) * asPolynomial (vector p (fun z => H (-z)))).coeff r +
      (asPolynomial (vector p F) * asPolynomial (vector p (fun z => H (-z)))).coeff (r+p) =
      (Balancing.correlation F H (r : ZMod p) : ℤ) := by
  rw [fold_product _ _ p r (le_of_eq (vector_length _ _))
    (le_of_eq (vector_length _ _)) hr]
  exact cyclic_correlation F H r hr
end ThreeSum.CyclicFold
