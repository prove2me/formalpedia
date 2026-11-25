-- Prove2me | solution 1 for P2M_PI_MirrorSection__monomialMatrix_conjTranspose_6ef84c3c3930
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:45:02.80199+00:00
-- url     : https://prove2.me/submissions/6423d852-7177-4930-aa8f-872645ffa1b0

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_IsMonomialConjTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.MirrorSection₂
open Formalism.FourierDecayAlt.C2
variable {m : ℕ}
namespace PI.MirrorSection₂
theorem _root_.solution (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) :
    (monoP w d)ᴴ = monoP w.symm (fun a => star (d (w.symm a))) := by
  ext i a
  simp only [conjTranspose_apply, monoP, of_apply]
  by_cases h : a = w i
  · rw [if_pos h, if_pos (by rw [h, Equiv.symm_apply_apply])]
    rw [h, Equiv.symm_apply_apply]
  · rw [if_neg h, star_zero, if_neg]
    intro h'
    exact h (by rw [h', Equiv.apply_symm_apply])
end PI.MirrorSection₂
