-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.exists_pk22LPSFamily_of_ramanujanCenteredEigenvalueBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:09:32.070389+00:00
-- url     : https://prove2.me/submissions/5165e0b6-17c1-41c7-99df-de9f3493e06a

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatibleLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCodeFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGoodFamilyAssembly
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_pk22LPSFamily_of_ramanujanComplexOperatorBound
import Theorems.Thm_QEC_Coding_SmallSetExpansion_hasMeanZeroComplexOperatorBound_of_abs_meanZeroEigenvalues_le
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
    (hRamanujan : ∀ (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ)
      (i : Fin (Module.finrank ℂ
        (EuclideanSpace ℂ (LPSVertexGroup hp hp4 n)))),
      |(SmallSetExpansion.centeredAdjacencyEuclidean_isSymmetric
          (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n)) (p + 1)
          (lpsRightCayleyGraph_isSymmetric hp hp4 n)).eigenvalues rfl i| ≤
        2 * Real.sqrt (p : ℝ)) :
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
  apply exists_pk22LPSFamily_of_ramanujanComplexOperatorBound
    F targetRate hRatePositive hRate
  intro p hp hp4 n
  apply SmallSetExpansion.hasMeanZeroComplexOperatorBound_of_abs_meanZeroEigenvalues_le
      (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n)) (p + 1)
      (lpsRightCayleyGraph_isSymmetric hp hp4 n) (by positivity)
  exact hRamanujan p hp hp4 n
end QEC.Coding.TannerLiftedProduct
