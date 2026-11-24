-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_finsum_log_adicAbv_f04fbb456bfa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:41.237659+00:00
-- url     : https://prove2.me/submissions/e43516ca-c251-4adb-9b74-eafff2d14ae2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup

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
open MvPolynomial MeasureTheory NumberField
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {x : K} (hx : x ≠ 0) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Real.log (NumberField.HeightOneSpectrum.adicAbv K v x) =
        -Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
  have hpos : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      0 < NumberField.HeightOneSpectrum.adicAbv K v x := fun v =>
    (NumberField.HeightOneSpectrum.adicAbv K v).pos hx
  rw [← Real.log_finprod hpos]
  have e : ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      NumberField.HeightOneSpectrum.adicAbv K v x = ∏ᶠ w : FinitePlace K, w x := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    refine finprod_congr fun v => ?_
    rw [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  rw [e, FinitePlace.prod_eq_inv_abs_norm hx, Rat.cast_inv, Real.log_inv]
end GroundTheory.Heights₂.Heights
