-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsIntegerThreeSquareAbs_fiber_card_le_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:55:34.462914+00:00
-- url     : https://prove2.me/submissions/bc19ab47-7d86-4933-aafd-118c86b78f29

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsInteger_mem_signed_pair_of_natAbs_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerThreeSquareSignedBox_card_le_eight

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (s : Finset ((ℤ × ℤ) × ℤ)) (a : (ℕ × ℕ) × ℕ) :
    (s.filter fun b => lpsIntegerThreeSquareAbs b=a).card ≤ 8 := by
  classical
  have hsub : (s.filter fun b => lpsIntegerThreeSquareAbs b=a) ⊆ lpsIntegerThreeSquareSignedBox a := by
    intro b hb
    have he := (Finset.mem_filter.mp hb).2
    have hx : b.1.1.natAbs=a.1.1 := congrArg (fun v : (ℕ × ℕ) × ℕ => v.1.1) he
    have hy : b.1.2.natAbs=a.1.2 := congrArg (fun v : (ℕ × ℕ) × ℕ => v.1.2) he
    have hz : b.2.natAbs=a.2 := congrArg Prod.snd he
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨lpsInteger_mem_signed_pair_of_natAbs_eq _ _ hx,
        lpsInteger_mem_signed_pair_of_natAbs_eq _ _ hy⟩,
      lpsInteger_mem_signed_pair_of_natAbs_eq _ _ hz⟩
  exact (Finset.card_le_card hsub).trans (lpsIntegerThreeSquareSignedBox_card_le_eight a)
end QEC.Coding.TannerLiftedProduct
