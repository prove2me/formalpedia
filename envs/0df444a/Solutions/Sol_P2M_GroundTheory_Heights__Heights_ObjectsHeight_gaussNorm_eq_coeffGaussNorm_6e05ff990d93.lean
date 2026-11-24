-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_gaussNorm_eq_coeffGaussNorm_6e05ff990d93
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:44.301857+00:00
-- url     : https://prove2.me/submissions/a4340e55-32d5-4e84-8cc5-fc49dd8e4f3d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm

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
theorem _root_.solution {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*} (f : MvPolynomial ι K) :
    gaussNorm v f = ReciprocityTheory.ChartRestriction.G.Geo.coeffGaussNorm (HeightOneSpectrum.adicAbv K v) f := by
  classical
  unfold gaussNorm ReciprocityTheory.ChartRestriction.G.Geo.coeffGaussNorm
  rcases f.support.eq_empty_or_nonempty with h | h
  · have : IsEmpty f.support := by rw [h]; infer_instance
    simp only [h, Real.iSup_of_isEmpty]
    rfl
  · have : Nonempty f.support := h.to_subtype
    have hb : BddAbove (Set.range fun m : f.support => HeightOneSpectrum.adicAbv K v (f.coeff m)) :=
      (Set.finite_range _).bddAbove
    apply le_antisymm
    · obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image f.support
        (fun m => HeightOneSpectrum.adicAbv K v (f.coeff m)) h
      refine le_trans ?_ (le_ciSup hb ⟨m, hm⟩)
      have hle : f.support.sup (fun m => (⟨HeightOneSpectrum.adicAbv K v (f.coeff m),
          AbsoluteValue.nonneg _ _⟩ : NNReal)) ≤
          ⟨HeightOneSpectrum.adicAbv K v (f.coeff m), AbsoluteValue.nonneg _ _⟩ :=
        Finset.sup_le fun b hb => hmax b hb
      exact NNReal.coe_le_coe.mpr hle
    · refine ciSup_le fun m => ?_
      have hle := Finset.le_sup (f := fun m => (⟨HeightOneSpectrum.adicAbv K v (f.coeff m),
          AbsoluteValue.nonneg _ _⟩ : NNReal)) m.2
      exact NNReal.coe_le_coe.mpr hle
end GroundTheory.Heights₂.Heights.ObjectsHeight
