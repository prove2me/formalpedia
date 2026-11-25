-- Prove2me | solution 1 for PI.UnitaryDimensionFormula.FrameAlg.h_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:36:19.583996+00:00
-- url     : https://prove2.me/submissions/291b4d8d-5fb2-4a93-bdb7-1ba681bc6008

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RankTwoDimensionFormula_IdxDcvAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open PI PI.UnitaryDimensionFormula PI.UnitaryDimensionFormula.FrameAlg
variable {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A) (J : Matrix n n A)
namespace PI.UnitaryDimensionFormula.FrameAlg
theorem _root_.solution (hJ : Formalism.UG.cT σ J = J) (hσ : ∀ a, σ (σ a) = a) (x y : n → A) :
    Formalism.UG.hform σ J y x = σ (Formalism.UG.hform σ J x y) := by
  have hJ' : ∀ i j, J i j = σ (J j i) := fun i j => by
    have h := congrFun (congrFun hJ i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at h
    exact h.symm
  simp only [Formalism.UG.hform, map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ' j i]
  ring
end PI.UnitaryDimensionFormula.FrameAlg
