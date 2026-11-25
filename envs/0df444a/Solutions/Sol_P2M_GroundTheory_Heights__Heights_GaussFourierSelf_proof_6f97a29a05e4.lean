-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussFourierSelf_proof_6f97a29a05e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:53.997935+00:00
-- url     : https://prove2.me/submissions/7224a773-7cb4-4dbb-ac3d-e9cc5fa5730b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussFourierSelf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussFourierSelf_ofReal_gauss_3cb7d6e7b62c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Real MeasureTheory
open scoped FourierTransform
namespace GroundTheory.Heights₂.Heights
namespace GaussFourierSelf
theorem _root_.solution : GaussFourierSelf.Statement := by
  intro g w
  have hb : 0 < (π : ℂ).re := by simpa using Real.pi_pos
  have hfun : (fun x : EuclideanSpace ℝ (Fin g) => ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ)) =
      fun x => Complex.exp (-(π : ℂ) * (‖x‖ : ℂ) ^ 2) := by
    funext x
    exact PGaussFourierSelf.ofReal_gauss x
  rw [hfun, fourier_gaussian_innerProductSpace hb w, PGaussFourierSelf.ofReal_gauss w]
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [div_self hpi, Complex.one_cpow, one_mul]
  congr 1
  field_simp
end GaussFourierSelf
end GroundTheory.Heights₂.Heights
