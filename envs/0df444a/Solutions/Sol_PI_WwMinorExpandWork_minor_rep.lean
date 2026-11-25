-- Prove2me | solution 1 for PI.WwMinorExpandWork.minor_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:35:08.826899+00:00
-- url     : https://prove2.me/submissions/53d88591-eaeb-41d5-b23d-8dc2a1e5e41e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwMinorExpand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorExpansion_WwMinorExpandMain
import Theorems.Thm_PI_WwMinorExpandWork_repM_zero
import Theorems.Thm_PI_WwMinorExpandWork_repM_add
import Theorems.Thm_PI_WwMinorExpandWork_repM_single
import Theorems.Thm_GenFrameSpan_det_mul_rect
import Theorems.Thm_GenFrameSpan_det_submatrix_fun


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.WwMinorExpandWork
open PI.WwMinorExpand
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ)
namespace PI.WwMinorExpandWork
theorem _root_.solution (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) :
    RepM N0 N1 s p (KM.minorXZ N0 N1 s p I) := by
  classical
  let A : Matrix (Fin p) (Fin N0) (MvPolynomial (KM.XZ Lt N0 N1) ℤ) :=
    Matrix.of fun i a => MvPolynomial.X (Sum.inl (s, (i : ℕ), a))
  let B : Matrix (Fin N0) (Fin p) (MvPolynomial (KM.XZ Lt N0 N1) ℤ) :=
    Matrix.of fun a k => MvPolynomial.X (Sum.inr (s, a, I k))
  have hAB : KM.minorXZ N0 N1 s p I = (A * B).det := by
    unfold KM.minorXZ
    congr 1
  have hA : ∀ J : Fin p ↪o Fin N0,
      (A.submatrix id J).det = MvPolynomial.rename Sum.inl (minX N0 s p J) := by
    intro J
    rw [minX, AlgHom.map_det]
    congr 1
    ext i k
    simp [A]
  rw [hAB, GenFrameSpan.det_mul_rect]
  refine Finset.sum_induction _ (RepM N0 N1 s p) (fun x y hx hy => repM_add N0 N1 s p hx hy)
    (repM_zero N0 N1 s p) (fun f _ => ?_)
  have hB : (∏ i, B (f i) i) =
      MvPolynomial.rename Sum.inr (∏ i, (MvPolynomial.X (s, f i, I i) :
        MvPolynomial (Lt × Fin N0 × Fin N1) ℤ)) := by
    simp [map_prod, B]
  rcases GenFrameSpan.det_submatrix_fun A f with h0 | ⟨J, e, he⟩
  · rw [h0, mul_zero]
    exact repM_zero N0 N1 s p
  · have : (∏ i, B (f i) i) * (A.submatrix id f).det =
        MvPolynomial.rename Sum.inl (minX N0 s p J) *
          MvPolynomial.rename Sum.inr ((e : MvPolynomial (Lt × Fin N0 × Fin N1) ℤ) *
            ∏ i, (MvPolynomial.X (s, f i, I i) : MvPolynomial (Lt × Fin N0 × Fin N1) ℤ)) := by
      rw [he, hA, hB, map_mul, map_intCast]
      ring
    rw [this]
    exact repM_single N0 N1 s p J _
end PI.WwMinorExpandWork
