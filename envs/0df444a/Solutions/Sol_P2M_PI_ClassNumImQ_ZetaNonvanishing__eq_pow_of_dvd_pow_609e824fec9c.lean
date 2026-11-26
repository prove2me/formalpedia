-- Prove2me | solution 1 for P2M_PI_ClassNumImQ_ZetaNonvanishing__eq_pow_of_dvd_pow_609e824fec9c
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:02:37.783241+00:00
-- url     : https://prove2.me/submissions/9ad0658d-da8c-405e-b3a4-dc2bf22c0617

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
theorem _root_.solution {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) {I : Ideal (𝓞 K)}
    {n : ℕ} (h : I ∣ P ^ n) : ∃ i ≤ n, I = P ^ i := by
  have hp : Prime P := Ideal.prime_of_isPrime hP0 hP
  obtain ⟨i, hi, h'⟩ := (dvd_prime_pow hp n).1 h
  exact ⟨i, hi, associated_iff_eq.1 h'⟩



