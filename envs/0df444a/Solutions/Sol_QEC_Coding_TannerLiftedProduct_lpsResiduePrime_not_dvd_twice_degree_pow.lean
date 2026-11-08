-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsResiduePrime_not_dvd_twice_degree_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:53:08.595041+00:00
-- url     : https://prove2.me/submissions/d61331cb-09d4-4b61-b8ae-dd3c0a07700a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {p : ℕ} (a : LPSResiduePrime p) (k : ℕ) :
    ¬(a.q : ℤ) ∣ 2*((p : ℤ)^k) := by
  intro hd
  have hdNat : a.q ∣ 2*p^k := by exact_mod_cast hd
  rcases a.prime.dvd_mul.mp hdNat with htwo | hpow
  · exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2)
      (by have hp := a.degreePrime.two_le; have hlarge := a.large; omega) htwo
  · exact Nat.not_dvd_of_pos_of_lt a.degreePrime.pos
      (by have hp := a.degreePrime.pos; have hlarge := a.large; omega)
      (a.prime.dvd_of_dvd_pow hpow)
end QEC.Coding.TannerLiftedProduct
