-- Prove2me | solution 1 for PI.WwMainW.block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:17:17.75665+00:00
-- url     : https://prove2.me/submissions/bf95a8d5-4674-41e2-81e5-90a982452443

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_FintypeColChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_DeXCBOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset Matrix
noncomputable section
open PI PI.WwMainW
open PI.WwMain PI.WwMain.KM
namespace PI.WwMainW
theorem _root_.solution (hCB : CBSorted) {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (z : Lt × Fin N0 × Fin N1 → ℂ_[l]) (y' : Lt → Fin N1 → ℕ → ℂ_[l]) (s : Lt) (p : ℕ) :
    Matrix.det (Matrix.of fun i j : Fin p => ∑ a : Fin N0,
        C (∑ b : Fin N1, z (s, a, b) * y' s b (j : ℕ)) *
          (X (s, (i : ℕ), a) : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l])) =
      ∑ J : Fin p ↪o Fin N1, C (Matrix.det (Matrix.of fun i j : Fin p => y' s (J i) (j : ℕ))) *
        chi l N0 N1 z (minorXZ N0 N1 s p J) := by
  unfold chi minorXZ
  calc _ = ((Matrix.of (fun (i : Fin p) (b : Fin N1) => (∑ a : Fin N0,
          (X (s, (i : ℕ), a) : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]) * C (z (s, a, b)) :
            MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l])) :
            Matrix (Fin p) (Fin N1) (MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l])) *
        (Matrix.of (fun (b : Fin N1) (j : Fin p) =>
          (C (y' s b (j : ℕ)) : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l])) :
            Matrix (Fin N1) (Fin p) (MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]))).det := by
        congr 1
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, Finset.sum_mul]
        first
          | (rw [Finset.sum_comm]
             exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)
          | exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
          | (rw [Finset.sum_comm]; ring)
    _ = _ := hCB _ _ _ _ _
    _ = _ := by
        refine Finset.sum_congr rfl fun J _ => ?_
        refine (mul_comm _ _).trans ?_
        congr 1
        · rw [RingHom.map_det]
          congr 1
          try (refine Matrix.ext fun i j => ?_; simp [Matrix.submatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply])
        · rw [RingHom.map_det]
          congr 1
          try (refine Matrix.ext fun i k => ?_; simp [Matrix.submatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
            map_sum, MvPolynomial.eval₂Hom_X'])
end PI.WwMainW
