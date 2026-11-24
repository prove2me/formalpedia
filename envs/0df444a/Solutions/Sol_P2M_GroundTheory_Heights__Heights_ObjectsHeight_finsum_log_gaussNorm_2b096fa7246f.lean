-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_finsum_log_gaussNorm_2b096fa7246f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:34.930832+00:00
-- url     : https://prove2.me/submissions/abd8200e-6e85-4f9b-98f4-33d734644e12

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_gaussNorm_eq_coeffGaussNorm_6e05ff990d93

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
open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ObjectsHeight
variable {n : ℕ}
variable {k : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsHeight
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {ι : Type*}
    (f : MvPolynomial ι K) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v f) =
      ∑ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K),
        Real.log (ReciprocityTheory.ChartRestriction.G.Geo.coeffGaussNorm v.1 f) := by
  have hv : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (FinitePlace.equivHeightOneSpectrum.symm v : FinitePlace K).val =
        HeightOneSpectrum.adicAbv K v := fun v => by
    ext x
    exact FinitePlace.norm_embedding v x
  show _ = ∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.ChartRestriction.G.Geo.coeffGaussNorm w.val f)
  rw [← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm]
  simp_rw [hv, gaussNorm_eq_coeffGaussNorm]
end GroundTheory.Heights₂.Heights.ObjectsHeight
