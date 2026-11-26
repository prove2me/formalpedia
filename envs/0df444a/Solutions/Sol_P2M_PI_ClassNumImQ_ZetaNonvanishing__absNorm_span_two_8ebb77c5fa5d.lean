-- Prove2me | solution 1 for P2M_PI_ClassNumImQ_ZetaNonvanishing__absNorm_span_two_8ebb77c5fa5d
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:02:35.660734+00:00
-- url     : https://prove2.me/submissions/9c6356fc-c7e9-4742-a806-bb1278d7334a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_SpanNatCastSupEqTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_GenBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.ClassNumImQ PI.ClassNumImQ.ZetaNonvanishing₂
variable {K : Type} [Field K] [NumberField K]
theorem _root_.solution (h2 : Module.finrank ℚ K = 2) (p : ℕ) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
  rw [Ideal.absNorm_span_singleton]
  have : Algebra.norm ℤ ((p : ℕ) : 𝓞 K) = (p : ℤ) ^ 2 := by
    have h := Algebra.norm_algebraMap_of_basis (Module.Free.chooseBasis ℤ (𝓞 K)) (p : ℤ)
    rw [← Module.finrank_eq_card_chooseBasisIndex, NumberField.RingOfIntegers.rank, h2] at h
    simpa using h
  rw [this]; simp [Int.natAbs_pow]



