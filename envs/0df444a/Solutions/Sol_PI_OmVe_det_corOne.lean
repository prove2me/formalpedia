-- Prove2me | solution 1 for PI.OmVe.det_corOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:22:08.029795+00:00
-- url     : https://prove2.me/submissions/772c5579-fccf-4584-98d5-ec9bd460e383

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_SingleMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmVe
open PI.VolStabSW Matrix
variable {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
namespace PI.OmVe
theorem _root_.solution {a : ℕ} (T : Matrix (Fin (a + 1)) (Fin (a + 1)) K) (i₀ : Fin (a + 1))
    (hr : ∀ j, T i₀ j = 0) (t : K) :
    (T + Matrix.single i₀ i₀ t).det = t * (T.submatrix i₀.succAbove i₀.succAbove).det := by

  rw [Matrix.det_succ_row _ i₀, Finset.sum_eq_single i₀
    (fun j _ hj => by simp [hr, Matrix.single_apply, Ne.symm hj]) (by simp)]
  have hsub : (T + Matrix.single i₀ i₀ t).submatrix i₀.succAbove i₀.succAbove =
      T.submatrix i₀.succAbove i₀.succAbove := by
    ext a b
    simp [Matrix.single_apply, (Fin.succAbove_ne i₀ a).symm]
  rw [hsub]
  simp [hr, Matrix.single_apply, ← two_mul, pow_mul]
end PI.OmVe
