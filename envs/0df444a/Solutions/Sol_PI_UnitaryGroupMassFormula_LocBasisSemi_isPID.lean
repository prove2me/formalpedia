-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocBasisSemi.isPID
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:41:31.681717+00:00
-- url     : https://prove2.me/submissions/7e82752b-5d45-4ff6-8cee-bd1998ea2697

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocBasisSemi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemilocalBasis_SmulMemOfMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemilocalBasis_IsPID

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocBasisSemi
namespace PI.UnitaryGroupMassFormula.LocBasisSemi
theorem _root_.solution (K : Type) [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime] :
    IsPrincipalIdealRing (A K p) := by
  have : IsDedekindDomain (A K p) := IsLocalization.isDedekindDomain (𝓞 K) (T_le K p) (A K p)
  have : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp.out)
  have hP0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  exact IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 K)
    (Ideal.span {(p : ℤ)}) hP0
end PI.UnitaryGroupMassFormula.LocBasisSemi
