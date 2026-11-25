-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_re_complexLinearCoeffs_dot_68aaf7064e75
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:55:55.800678+00:00
-- url     : https://prove2.me/submissions/315b838f-e042-4e0b-ac9c-1aa83a4d13f6

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComplexTaylor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PComplexTaylorTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Filter Topology Asymptotics ReciprocityTheory.AnForm Matrix Metric
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {D : ℕ} (L : (Fin D → ℂ) →L[ℝ] ℝ) (z : Fin D → ℂ) :
    (complexLinearCoeffs L ⬝ᵥ z).re = L z := by
  have hz : z = ∑ j, ((z j).re • (Pi.single j 1 : Fin D → ℂ) +
      (z j).im • (Complex.I • (Pi.single j 1 : Fin D → ℂ))) := by
    ext k
    apply Complex.ext <;> simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
  conv_rhs => rw [hz]
  simp only [map_sum, map_add, map_smul, dotProduct, Complex.re_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [complexLinearCoeffs, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring
end GroundTheory.Heights₂.Heights.HilbertSamuel
