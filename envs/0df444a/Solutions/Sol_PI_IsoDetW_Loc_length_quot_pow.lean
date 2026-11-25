-- Prove2me | solution 1 for PI.IsoDetW.Loc.length_quot_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:44:18.74198+00:00
-- url     : https://prove2.me/submissions/58a7a927-ae06-4aa5-b2ff-4582b6f631c3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoDetW PI.IsoDetW.Loc
open PI.IsoDetDefs IsDedekindDomain
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
namespace PI.IsoDetW.Loc
theorem _root_.solution (P : HeightOneSpectrum R) (k : ℕ) :
    Module.length R (R ⧸ P.asIdeal ^ k) = k := by
  haveI := P.isMaximal
  let Rₚ := Localization.AtPrime P.asIdeal
  haveI : IsDiscreteValuationRing Rₚ :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R P.ne_bot Rₚ
  let e := IsLocalization.AtPrime.equivQuotMaximalIdealPow P.asIdeal Rₚ k
  rw [e.toLinearEquiv.length_eq]
  have hs1 : Function.Surjective (algebraMap R (Rₚ ⧸ IsLocalRing.maximalIdeal Rₚ ^ k)) := by
    intro q
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e.symm q)
    refine ⟨r, ?_⟩
    have h1 : e (Ideal.Quotient.mk _ r) = q := by rw [hr]; simp
    rw [← h1, IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk]
    rfl
  have hs2 : Function.Surjective (algebraMap Rₚ (Rₚ ⧸ IsLocalRing.maximalIdeal Rₚ ^ k)) :=
    Ideal.Quotient.mk_surjective
  rw [Module.length_eq_of_surjective hs1, ← Module.length_eq_of_surjective hs2,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
end PI.IsoDetW.Loc
