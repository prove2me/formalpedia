-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.cubic_times_four_hits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:00:31.487309+00:00
-- url     : https://prove2.me/submissions/6134ff15-f4fe-49f1-8fae-e9f3be8c6b5d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventProbability

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {lambda C B : ℝ} (hl : 0 < lambda) :
    C*lambda^3*(B/lambda)^4 = (C*B^4)/lambda := by
  field_simp [hl.ne']
end QEC.Coding.BDL26RandomPerturbation
