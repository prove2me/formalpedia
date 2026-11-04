-- Prove2me | solution 1 for ThreeSum.CyclicFold.cyclic_correlation_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:41:37.747562+00:00
-- url     : https://prove2.me/submissions/b18d1260-0505-4971-afc1-c3415b023953

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_Submission_ThreeSum_CyclicFold
import Theorems.Thm_ThreeSum_CyclicFold_vector_getD
import Theorems.Thm_ThreeSum_CyclicFold_sum_range_zmod
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD



set_option autoImplicit false
open ThreeSum ThreeSum.CyclicFold
open Finset Polynomial Karatsuba
open scoped BigOperators
namespace ThreeSum.CyclicFold
theorem _root_.solution {p : ℕ} [NeZero p]
    (F H : ZMod p → ℕ) (r : ℕ) (hr : r < p) :
    cyclic p (vector p F) (vector p (fun z => H (-z))) r =
      (Balancing.correlation F H (r : ZMod p) : ℤ) := by
  have heq (i j : ℕ) : (i + j) % p = r ↔
      (i : ZMod p) + (j : ZMod p) = (r : ZMod p) := by
    rw [← Nat.cast_add, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hr]
  calc
    _ = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range p,
        if (i : ZMod p) + (j : ZMod p) = (r : ZMod p)
        then (F (i : ZMod p) : ℤ) * (H (-(j : ZMod p)) : ℤ) else 0 := by
      unfold cyclic
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      simp only [vector_getD p F i (mem_range.mp hi),
        vector_getD p (fun z => H (-z)) j (mem_range.mp hj), heq]
    _ = ∑ i : ZMod p, ∑ j : ZMod p,
        if i + j = (r : ZMod p) then (F i : ℤ) * (H (-j) : ℤ) else 0 := by
      have hinner (i : ℕ) :
          (∑ j ∈ Finset.range p, if (i : ZMod p) + (j : ZMod p) = (r : ZMod p)
            then (F (i : ZMod p) : ℤ) * (H (-(j : ZMod p)) : ℤ) else 0) =
          ∑ j : ZMod p, if (i : ZMod p) + j = (r : ZMod p)
            then (F (i : ZMod p) : ℤ) * (H (-j) : ℤ) else 0 :=
        sum_range_zmod (fun j => if (i : ZMod p) + j = (r : ZMod p)
          then (F (i : ZMod p) : ℤ) * (H (-j) : ℤ) else 0)
      simp_rw [hinner]
      exact sum_range_zmod (fun i => ∑ j : ZMod p,
        if i + j = (r : ZMod p) then (F i : ℤ) * (H (-j) : ℤ) else 0)
    _ = ∑ i : ZMod p, (F i : ℤ) * (H (i - (r : ZMod p)) : ℤ) := by
      apply sum_congr rfl
      intro i hi
      have hj (j : ZMod p) : i + j = (r : ZMod p) ↔ j = (r : ZMod p) - i := by
        rw [eq_sub_iff_add_eq, add_comm]
      simp_rw [hj]
      simp
    _ = _ := by simp [Balancing.correlation]
end ThreeSum.CyclicFold
