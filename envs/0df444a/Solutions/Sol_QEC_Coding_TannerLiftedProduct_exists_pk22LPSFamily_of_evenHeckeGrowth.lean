-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.exists_pk22LPSFamily_of_evenHeckeGrowth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:13:48.91774+00:00
-- url     : https://prove2.me/submissions/5186d4e4-3d12-4efe-b46e-b50180f3bb95

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatibleLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCodeFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGoodFamilyAssembly
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_pk22LPSFamily_of_ramanujanCenteredEigenvalueBound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_le_two_mul_sqrt_of_lpsHeckePolynomial_even_isBigO
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_eq_prime_add_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRightCayleyGraph_isSymmetric


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
attribute [local instance] QEC.Coding.TannerLiftedProduct.pk22LPSFamilyQubitDecidableEq
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (F : Type) [Field F] [Fintype F]
    (targetRate : ℝ) (hRatePositive : 0 < targetRate)
    (hRate : targetRate < 1)
    (hHeckeGrowth : ∀ (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
      (n : ℕ)
      (i : Fin (Module.finrank ℂ
        (EuclideanSpace ℂ (LPSVertexGroup hp hp4 n))))
      (t : ℝ), Real.sqrt (p : ℝ) < t →
      (fun m : ℕ =>
        (lpsHeckePolynomial ℝ (p : ℝ) (2 * m)).eval
          ((SmallSetExpansion.centeredAdjacencyEuclidean_isSymmetric
            (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n)) (p + 1)
            (lpsRightCayleyGraph_isSymmetric hp hp4 n)).eigenvalues rfl i))
        =O[Filter.atTop] fun m : ℕ => t ^ (2 * m)) :
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
  apply exists_pk22LPSFamily_of_ramanujanCenteredEigenvalueBound
    F targetRate hRatePositive hRate
  intro p hp hp4 n i
  exact abs_le_two_mul_sqrt_of_lpsHeckePolynomial_even_isBigO
    (Nat.cast_pos.mpr hp.pos) _ (hHeckeGrowth p hp hp4 n i)
end QEC.Coding.TannerLiftedProduct
