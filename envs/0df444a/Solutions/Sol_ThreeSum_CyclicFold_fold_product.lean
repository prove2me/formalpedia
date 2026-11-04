-- Prove2me | solution 1 for ThreeSum.CyclicFold.fold_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:41:36.709801+00:00
-- url     : https://prove2.me/submissions/5c79bff6-f922-4e4f-be6e-f4a17ae4dcbb

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_Submission_ThreeSum_CyclicFold
import Theorems.Thm_ThreeSum_CyclicFold_product_coeff_double
import Theorems.Thm_ThreeSum_CyclicFold_mod_indicator

set_option autoImplicit false
open ThreeSum ThreeSum.CyclicFold
open Finset Polynomial Karatsuba
open scoped BigOperators
namespace ThreeSum.CyclicFold
theorem _root_.solution (as bs : List ℤ) (p r : ℕ)
    (ha : as.length ≤ p) (hb : bs.length ≤ p) (hr : r < p) :
    (asPolynomial as * asPolynomial bs).coeff r +
      (asPolynomial as * asPolynomial bs).coeff (r + p) = cyclic p as bs r := by
  rw [product_coeff_double as bs p ha hb, product_coeff_double as bs p ha hb]
  rw [← sum_add_distrib]
  unfold cyclic
  apply sum_congr rfl
  intro i hi
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  exact mod_indicator (mem_range.mp hi) (mem_range.mp hj) hr _
end ThreeSum.CyclicFold
