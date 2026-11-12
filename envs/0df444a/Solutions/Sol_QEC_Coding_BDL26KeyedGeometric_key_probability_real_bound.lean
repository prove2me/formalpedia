-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.key_probability_real_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:07:27.470122+00:00
-- url     : https://prove2.me/submissions/d5ce476c-1d56-4b02-b1bc-e9be84a5b4c7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricEvents
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ProbabilityDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ConcreteParameters
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricProbability
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_event_probability_real_decay
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_capCutoff_bounds


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
namespace QEC.Coding.BDL26KeyedGeometric
theorem _root_.solution (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) (e : KeyEvent P key hk J (anchorRadius p.m)) :
    (Measure.pi (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))).real
      (localEvent (keySupport P key hk J (anchorRadius p.m))
        (keyBad P key hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e) ≤
      probabilityCoefficient (6*p.m) (capCutoff p.m)/(p.lambda : ℝ) := by
  have ha : 0 < 6*p.m := by have hm := p.m_two; omega
  exact key_event_probability_real_decay P key hk J (anchorRadius p.m) (6*p.m)
    p.lambda ha p.lambda_one e (capCutoff_bounds p.m_two).1 (capCutoff_bounds p.m_two).2
end QEC.Coding.BDL26KeyedGeometric
