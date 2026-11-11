-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.finite_cap_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:53:15.439563+00:00
-- url     : https://prove2.me/submissions/ba47dcc6-a6b8-44f5-a8d6-31681369e421

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Coloring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_TriangleHit
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Sampling
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capDisplacementLaw_capSupport
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_measurableSet_displacementCap


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) {R c : ℝ} (hR : 0 < R)
    (hc : c < 1) :
    ∀ᵐ p ∂Measure.pi (vertexLaw P R c), ∀ v,
      p v ∈ displacementCap R (vertexAxis P v) c := by
  letI (v : Vertex P) := vertexLaw_probability P R hc v
  apply ae_all_iff.mpr
  intro v
  have hm := measurableSet_displacementCap R (vertexAxis P v) c
  apply (mem_ae_iff_prob_eq_one (hm.preimage (measurable_pi_apply v))).mpr
  have hp := measurePreserving_eval (vertexLaw P R c) v
  rw [hp.measure_preimage hm.nullMeasurableSet]
  exact capDisplacementLaw_capSupport hR (vertexAxis P v) hc
end QEC.Coding.BDL26RandomPerturbation
