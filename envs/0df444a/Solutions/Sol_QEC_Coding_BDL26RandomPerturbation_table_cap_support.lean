-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.table_cap_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:53:42.294854+00:00
-- url     : https://prove2.me/submissions/d2cb251d-0b1f-4270-aac7-e395ca64344f

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
    letI (v : Vertex P) := vertexLaw_probability P R hc v
    ∀ᵐ T ∂tableLaw (vertexLaw P R c), ∀ p : Vertex P × ℕ,
      T p ∈ displacementCap R (vertexAxis P p.1) c := by
  letI (v : Vertex P) := vertexLaw_probability P R hc v
  apply ae_all_iff.mpr
  intro p
  have hm := measurableSet_displacementCap R (vertexAxis P p.1) c
  apply (mem_ae_iff_prob_eq_one (hm.preimage (measurable_pi_apply p))).mpr
  change (Measure.infinitePi (fun p : Vertex P × ℕ => vertexLaw P R c p.1))
    ((fun T => T p) ⁻¹' displacementCap R (vertexAxis P p.1) c) = 1
  have hp := measurePreserving_eval_infinitePi (fun p : Vertex P × ℕ => vertexLaw P R c p.1) p
  rw [hp.measure_preimage hm.nullMeasurableSet]
  exact capDisplacementLaw_capSupport hR (vertexAxis P p.1) hc
end QEC.Coding.BDL26RandomPerturbation
