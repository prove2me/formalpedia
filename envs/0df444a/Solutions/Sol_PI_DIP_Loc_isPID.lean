-- Prove2me | solution 1 for PI.DIP.Loc.isPID
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:34:18.580939+00:00
-- url     : https://prove2.me/submissions/80c96c92-147c-4ad7-b3d1-153163cf9e56

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_SmulMemOfMemSpan

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
open PI PI.DIP PI.DIP.Loc
variable (K : Type) [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]
variable {K p}
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.DIP.Loc
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
end PI.DIP.Loc
