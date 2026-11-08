-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.exists_pk22LPSFamily_of_ramanujan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:44:44.899674+00:00
-- url     : https://prove2.me/submissions/f02734c3-f346-442d-96ee-ab3cc68400fd

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatibleLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCodeFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGoodFamilyAssembly
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_pk22LPSFamily_of_fourSqrtBound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_eq_prime_add_one


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
attribute [local instance] QEC.Coding.TannerLiftedProduct.pk22LPSFamilyQubitDecidableEq
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (F : Type) [Field F] [Fintype F]
    (targetRate : ℝ) (hRatePositive : 0 < targetRate)
    (hRate : targetRate < 1)
    (hRamanujan : ∀ (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ),
      SmallSetExpansion.HasMeanZeroBilinearBound
        (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n))
        (2 * Real.sqrt (p : ℝ))) :
    ∃ (t : ℕ)
      (a : CompatibleDegreePrime (pk22LocalWidth (Nat.card F) t))
      (h h' : Matrix (PK22Check (Nat.card F) t a)
        (PK22Direction (Nat.card F) t a) F),
      let hCount := card_lpsQuaternionShell_eq_prime_add_one
        a.prime a.oneModFour
      QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily
          (lpsSemanticFamily a.prime a.oneModFour hCount h h') ∧
        QEC.QLDPC.HasEventualRateAtLeast
          (lpsSemanticFamily a.prime a.oneModFour hCount h h') targetRate := by
  apply exists_pk22LPSFamily_of_fourSqrtBound F targetRate hRatePositive hRate
  intro p hp hp4 n f g hf hg
  have hBound := hRamanujan p hp hp4 n f g hf hg
  have hFactor : 0 ≤ Real.sqrt
      ((∑ v, (f v) ^ 2) * ∑ v, (g v) ^ 2) := Real.sqrt_nonneg _
  have hScale : 2 * Real.sqrt (p : ℝ) ≤
      4 * Real.sqrt (p : ℝ) := by
    nlinarith [Real.sqrt_nonneg (p : ℝ)]
  exact hBound.trans (mul_le_mul_of_nonneg_right hScale hFactor)
end QEC.Coding.TannerLiftedProduct
