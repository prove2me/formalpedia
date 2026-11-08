-- Prove2me | solution 2 for ProbabilityTheory.LevyKhintchineTriple.exponent_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:28:42.416858+00:00
-- url     : https://prove2.me/submissions/3527c5d2-3d5b-424c-918c-62ce63d5d234

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_levy_foundations_isLevyMeasure
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_compensatedIntegrand
import Definitions.Def_levy_foundations_exponent
import Theorems.Thm_levy_foundations_exponentContinuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

/-- Transport exponent continuity across the source-identical Lévy triple presentations. -/
theorem solution (T : LevyKhintchineTriple) : Continuous T.exponent := by
  let U : LevyFoundations.LevyKhintchineTriple :=
    ⟨T.drift, T.gaussianVariance, T.levyMeasure, T.levyMeasure_isLevyMeasure⟩
  have heq : T.exponent = LevyFoundations.exponent U := by
    funext ξ
    rfl
  rw [heq]
  exact levy_foundations_exponentContinuous U
