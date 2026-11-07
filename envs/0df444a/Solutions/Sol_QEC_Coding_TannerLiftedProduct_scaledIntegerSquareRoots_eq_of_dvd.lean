-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.scaledIntegerSquareRoots_eq_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:39:23.431202+00:00
-- url     : https://prove2.me/submissions/69b0eecf-0dc9-440e-bb2a-d421e07e6bff

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.RingTheory.PowerSeries.Substitution
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {m n : ℕ} (hm : 0 < m) (hdiv : m ^ 2 ∣ n) :
    scaledIntegerSquareRoots m n = integerSquareRoots (n / m ^ 2) := by
  ext z
  rw [mem_scaledIntegerSquareRoots_iff hm,
    mem_integerSquareRoots_iff]
  have hmSq : (m ^ 2 : ℕ) ≠ 0 := pow_ne_zero 2 hm.ne'
  have hcast : (((m ^ 2 : ℕ) : ℤ)) = (m : ℤ) ^ 2 := by norm_num
  have hn : m ^ 2 * (n / m ^ 2) = n := Nat.mul_div_cancel' hdiv
  constructor
  · intro hz
    apply mul_left_cancel₀ (show (((m ^ 2 : ℕ) : ℤ)) ≠ 0 by
      exact_mod_cast hmSq)
    rw [hcast]
    calc
      (m : ℤ) ^ 2 * z ^ 2 = (n : ℤ) := hz
      _ = (((m ^ 2) * (n / m ^ 2) : ℕ) : ℤ) := by rw [hn]
      _ = ((m ^ 2 : ℕ) : ℤ) * ((n / m ^ 2 : ℕ) : ℤ) := by
        push_cast
        rfl
  · intro hz
    rw [← hcast]
    calc
      ((m ^ 2 : ℕ) : ℤ) * z ^ 2 =
          ((m ^ 2 : ℕ) : ℤ) * ((n / m ^ 2 : ℕ) : ℤ) := by
        rw [hz]
      _ = (((m ^ 2) * (n / m ^ 2) : ℕ) : ℤ) := by
        push_cast
        rfl
      _ = (n : ℤ) := by rw [hn]
end QEC.Coding.TannerLiftedProduct
