-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsIntegerOffset_toNat_facts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:59:50.437045+00:00
-- url     : https://prove2.me/submissions/b12b2ca1-bc9e-43c0-b51c-55b7b6ad5345

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
theorem _root_.solution (x : ℤ) (r M : ℕ)
    (hb : -(r : ℤ) ≤ x ∧ x ≤ (r : ℤ)) (hd : (M : ℤ) ∣ x+(r : ℤ)) :
    ((x+(r : ℤ)).toNat : ℤ)=x+(r : ℤ) ∧ (x+(r : ℤ)).toNat ≤ 2*r ∧
      M ∣ (x+(r : ℤ)).toNat := by
  have hc : ((x+(r : ℤ)).toNat : ℤ)=x+(r : ℤ) := Int.toNat_of_nonneg (by omega)
  refine ⟨hc, ?_, ?_⟩
  · have hh : ((x+(r : ℤ)).toNat : ℤ) ≤ ((2*r : ℕ) : ℤ) := by rw [hc]; omega
    exact_mod_cast hh
  · have hh : (M : ℤ) ∣ ((x+(r : ℤ)).toNat : ℤ) := by rw [hc]; exact hd
    exact_mod_cast hh
end QEC.Coding.TannerLiftedProduct
