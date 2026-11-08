-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsTraceQuadraticShell_firstCoordinate_congruence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:06:45.744414+00:00
-- url     : https://prove2.me/submissions/0d480191-3889-41f6-8a5b-6cf031aa03a3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTraceQuadraticForm_decompose
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrimeSquare_dvd_difference_or_sum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q r : ℕ) (hq : q.Prime)
    (hqr : ¬(q : ℤ) ∣ 2*(r : ℤ)) (t : LPSQuaternion)
    (ht : t ∈ lpsTraceQuadraticShell q (r^2)) :
    (q : ℤ)^2 ∣ t.a-(r : ℤ) ∨ (q : ℤ)^2 ∣ t.a+(r : ℤ) := by
  have hn := (mem_lpsTraceQuadraticShell_iff hq.pos t).mp ht
  rw [lpsTraceQuadraticForm_decompose] at hn
  have hn' : t.a^2+4*(q : ℤ)^2*(t.b^2+t.c^2+t.d^2)=(r : ℤ)^2 := by exact_mod_cast hn
  apply lpsPrimeSquare_dvd_difference_or_sum (q : ℤ) t.a (r : ℤ)
    (Nat.prime_iff_prime_int.mp hq) hqr
  refine ⟨-(4*(t.b^2+t.c^2+t.d^2)), ?_⟩
  linear_combination hn'
end QEC.Coding.TannerLiftedProduct
