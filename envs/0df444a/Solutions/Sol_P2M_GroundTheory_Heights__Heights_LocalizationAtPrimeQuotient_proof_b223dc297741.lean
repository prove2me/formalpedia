-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalizationAtPrimeQuotient_proof_b223dc297741
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:45.138806+00:00
-- url     : https://prove2.me/submissions/d82ae1ba-4187-43a7-a659-22a737f8e6f2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalizationAtPrimeQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalizationAtPrimeQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
universe u
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace LocalizationAtPrimeQuotient
theorem _root_.solution : LocalizationAtPrimeQuotient.Statement.{u} := by
  intro A _ I T P _ W _ hP
  let Q := A ⧸ I
  let B := Localization.AtPrime W ⧸ I.map (algebraMap A (Localization.AtPrime W))

  have hsub : (P.comap (algebraMap Q (Localization T))).primeCompl =
      Algebra.algebraMapSubmonoid Q W.primeCompl := by
    have hmem : ∀ r : A, Ideal.Quotient.mk I r ∈ P.comap (algebraMap Q (Localization T)) ↔ r ∈ W := by
      intro r; rw [← hP]; exact Iff.rfl
    have hIW : I ≤ W := fun r hr => by
      rw [← hmem, Ideal.Quotient.eq_zero_iff_mem.2 hr]; exact Ideal.zero_mem _
    ext q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    have h1 : Ideal.Quotient.mk I r ∈ (P.comap (algebraMap Q (Localization T))).primeCompl ↔ r ∉ W :=
      not_congr (hmem r)
    rw [h1]
    constructor
    · intro hr; exact ⟨r, hr, rfl⟩
    · rintro ⟨r', hr', he⟩ hr
      apply hr'
      have : r' - r ∈ I := Ideal.Quotient.eq.1 he
      simpa using W.add_mem (hIW this) hr
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid Q W.primeCompl) (Localization.AtPrime P) := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization T
      (Localization.AtPrime P) P
    rw [IsLocalization.AtPrime, hsub] at this
    exact this
  let e := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid Q W.primeCompl)
    (Localization.AtPrime P) B
  refine ⟨e.toRingEquiv, fun a => ?_⟩
  have h2 : algebraMap (Localization T) (Localization.AtPrime P)
      (algebraMap Q (Localization T) (Ideal.Quotient.mk I a)) =
      algebraMap Q (Localization.AtPrime P) (Ideal.Quotient.mk I a) :=
    (IsScalarTower.algebraMap_apply Q (Localization T) (Localization.AtPrime P) _).symm
  rw [h2]
  exact e.commutes (Ideal.Quotient.mk I a)
end LocalizationAtPrimeQuotient
end GroundTheory.Heights₂.Heights
