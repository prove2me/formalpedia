-- Prove2me | solution 1 for PI.SqPair.LCP.blk_unimod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:22:24.000054+00:00
-- url     : https://prove2.me/submissions/14e73f95-f9bc-48bc-bcfe-d27286f072cc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_FiniteAdeleIdempotentOfFMulSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
variable {R : Type} [CommRing R] [StarRing R]
namespace PI.SqPair.LCP
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ]
    {A u : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R} {A₁ : Matrix κ κ R} (hu : IsUnit u.det)
    (hA : Unimod A) (h : uᴴ * A * u = fromBlocks hyp 0 0 A₁) : Unimod A₁ := by
  constructor
  · have h1 : (uᴴ * A * u)ᴴ = uᴴ * A * u := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, hA.1, Matrix.mul_assoc]
    rw [h, fromBlocks_conjTranspose] at h1
    exact (fromBlocks_inj.1 h1).2.2.2
  · have h1 : IsUnit (uᴴ * A * u).det := by
      rw [det_mul, det_mul, det_conjTranspose]; exact (hu.star.mul hA.2).mul hu
    rw [h, det_fromBlocks_zero₂₁] at h1
    exact isUnit_of_mul_isUnit_right h1
end PI.SqPair.LCP
