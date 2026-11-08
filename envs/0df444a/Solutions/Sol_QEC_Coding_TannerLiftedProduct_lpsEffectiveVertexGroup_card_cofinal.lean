-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveVertexGroup_card_cofinal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:26:56.671197+00:00
-- url     : https://prove2.me/submissions/107c58fd-74e9-4859-8353-36cd113c8e9d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lt_lpsEffectiveResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSResiduePrime_q_le_two_mul_card_psl

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) :
    ∀ N : ℕ, ∃ n, N ≤ Fintype.card (LPSEffectiveVertexGroup hp hp4 n) := by
  intro N
  refine ⟨2 * N, ?_⟩
  have hLarge := lt_lpsEffectiveResiduePrimeAt_q hp hp4 (2 * N)
  have hCard := (lpsEffectiveResiduePrimeAt hp hp4 (2 * N)).q_le_two_mul_card_psl
  change N ≤ Fintype.card PSL(2, ZMod (lpsEffectiveResiduePrimeAt hp hp4 (2 * N)).q)
  omega
end QEC.Coding.TannerLiftedProduct
