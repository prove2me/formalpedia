-- Prove2me | solution 1 for PI.WwCauchyBinetWork.factor_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:18:38.174577+00:00
-- url     : https://prove2.me/submissions/509500a1-1b64-4859-8003-125c091db493

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwCauchyBinet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CauchyBinet_WwCauchyBinetMain
import Theorems.Thm_PI_IsoDerivBFintype_cauchyBinet


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.WwCauchyBinetWork
open PI.WwCauchyBinet
namespace PI.WwCauchyBinetWork
theorem _root_.solution {Lt k : Type} [CommRing k] (N : ℕ) (s : Lt) (h : ℕ) (y : Fin N → ℕ → k) :
    Matrix.det (Matrix.of fun i j : Fin h =>
      ∑ a : Fin N, MvPolynomial.C (y a (j : ℕ)) * (MvPolynomial.X (s, (i : ℕ), a) : MvPolynomial (Lt × ℕ × Fin N) k))
    = ∑ I : Fin h ↪o Fin N,
        MvPolynomial.C (Matrix.det (Matrix.of fun i j : Fin h => y (I i) (j : ℕ))) *
        MvPolynomial.map (Int.castRingHom k) (Matrix.det (Matrix.of fun i j : Fin h =>
          (MvPolynomial.X (s, (i : ℕ), I j) : MvPolynomial (Lt × ℕ × Fin N) ℤ))) := by
  have hM : (Matrix.of fun i j : Fin h =>
      ∑ a : Fin N, MvPolynomial.C (y a (j : ℕ)) *
        (MvPolynomial.X (s, (i : ℕ), a) : MvPolynomial (Lt × ℕ × Fin N) k)) =
      (Matrix.of fun (i : Fin h) (a : Fin N) =>
        (MvPolynomial.X (s, (i : ℕ), a) : MvPolynomial (Lt × ℕ × Fin N) k)) *
      (Matrix.of fun (a : Fin N) (j : Fin h) =>
        (MvPolynomial.C (y a (j : ℕ)) : MvPolynomial (Lt × ℕ × Fin N) k)) := by
    ext i j
    simp [Matrix.mul_apply, mul_comm]
  rw [hM, PI.IsoDerivBFintype.cauchyBinet]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [mul_comm]
  congr 1
  · rw [RingHom.map_det]
    congr 1
  · rw [RingHom.map_det]
    congr 1
    ext i j
    simp
end PI.WwCauchyBinetWork
