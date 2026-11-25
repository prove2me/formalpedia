-- Prove2me | solution 1 for P2M_Formalism_HermitianLatticeCounting_P_det_submatrix_consRow_succAbove__ac784a4c22c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:43:42.860303+00:00
-- url     : https://prove2.me/submissions/489f08ce-1dc8-4328-bd46-6b546a8583a5

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_submatrix_consRow_succAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {R : Type*} [CommRing R] {r : ℕ} (Y : Matrix (Fin r) (Fin (r + 1)) R)
    (u : Fin (r + 1) → R) (b₀ : Fin (r + 1)) (a : Fin r) :
    ((consRowMatrix u Y).submatrix a.succ.succAbove b₀.succAbove).det =
      (-1) ^ (a : ℕ) * ∑ c, u (b₀.succAbove c) * (Y.submatrix id b₀.succAbove).adjugate c a := by
  cases r with
  | zero => exact a.elim0
  | succ n => exact det_submatrix_consRow_succAbove Y u b₀ a
end Formalism.HermitianLatticeCounting.P
