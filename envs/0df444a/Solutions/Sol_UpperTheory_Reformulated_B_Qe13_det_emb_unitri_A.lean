-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:09.375336+00:00
-- url     : https://prove2.me/submissions/024e25e2-6615-44d2-a925-b7ebd8293831

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetEmbUnitriA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qe13
theorem _root_.solution :
    ∀ {n : ℕ} (g : GL (Fin n) ℂ),
      (∀ (i j : Fin n), j < i → (↑g : Matrix (Fin n) (Fin n) ℂ) i j = (0 : ℂ)) →
        (∀ (i : Fin n), (↑g : Matrix (Fin n) (Fin n) ℂ) i i = (1 : ℂ)) →
          (Matrix.GeneralLinearGroup.det : GL (Fin (n + (1 : ℕ))) ℂ → ℂˣ)
              ((UpperTheory.Reformulated.B.Qe13.embGL ℂ n (n + (1 : ℕ)) rfl : GL (Fin n) ℂ → GL (Fin (n + (1 : ℕ))) ℂ) g) =
            (1 : ℂˣ) := by
  intro n g hlow hdiag
  have htri : (↑g : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id := fun i j hij => hlow i j hij
  have hg : (↑g : Matrix (Fin n) (Fin n) ℂ).det = 1 := by
    rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_one fun i _ => hdiag i
  apply Units.ext
  change Matrix.det (Matrix.reindex (finSumFinEquiv.trans (finCongr rfl)) (finSumFinEquiv.trans (finCongr rfl))
    (Matrix.fromBlocks (↑g : Matrix (Fin n) (Fin n) ℂ) (0 : Matrix (Fin n) (Fin 1) ℂ)
      (0 : Matrix (Fin 1) (Fin n) ℂ) (1 : Matrix (Fin 1) (Fin 1) ℂ))) = 1
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, hg, Matrix.det_one, mul_one]
end UpperTheory.Reformulated.B.Qe13
