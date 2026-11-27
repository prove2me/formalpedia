-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalizeQuotientStages_proof_ba485756d6ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:02:56.344935+00:00
-- url     : https://prove2.me/submissions/eb08de1b-0bf2-4daf-b4c6-78aace47bdb4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalizeQuotientStages
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalizeQuotientStages
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_length_self_eq_of_ringEquiv_a79d4441b24a

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
namespace LocalizeQuotientStages
theorem _root_.solution : LocalizeQuotientStages.Statement.{u} := by
  intro R _ m W I _ _ hWm hIW P _ hP
  let Q := R ⧸ I
  let B := Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))
  let T := Localization.AtPrime W ⧸ I.map (algebraMap R (Localization.AtPrime W))

  have hdisj : Disjoint (m.primeCompl : Set R) (W : Set R) :=
    Set.disjoint_left.2 fun a ha hW => ha (hWm hW)
  have hPR : P.comap (algebraMap R B) = W := by
    rw [IsScalarTower.algebraMap_eq R (Localization.AtPrime m) B, ← Ideal.comap_comap,
      Ideal.Quotient.algebraMap_eq, ← hP,
      ← Ideal.map_map, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 (Ideal.map_mono hIW)]
    exact IsLocalization.under_map_of_isPrime_disjoint m.primeCompl _ ‹W.IsPrime› hdisj

  have hsub : (P.comap (algebraMap Q B)).primeCompl =
      Algebra.algebraMapSubmonoid Q W.primeCompl := by
    ext q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    have h1 : Ideal.Quotient.mk I r ∈ (P.comap (algebraMap Q B)).primeCompl ↔ r ∉ W := by
      rw [← hPR]; exact Iff.rfl
    rw [h1]
    constructor
    · intro hr; exact ⟨r, hr, rfl⟩
    · rintro ⟨r', hr', he⟩ hr
      apply hr'
      have : r' - r ∈ I := Ideal.Quotient.eq.1 he
      simpa using W.add_mem (hIW this) hr
  have hBP : IsLocalization (Algebra.algebraMapSubmonoid Q W.primeCompl)
      (Localization.AtPrime P) := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid Q m.primeCompl) (Localization.AtPrime P) P
    rw [IsLocalization.AtPrime, hsub] at this
    exact this
  let e := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid Q W.primeCompl)
    (Localization.AtPrime P) T
  exact (length_self_eq_of_ringEquiv (A := Localization.AtPrime P) (C := T) e.toRingEquiv).trans
    (Module.length_eq_of_surjective (R := T) (S := Localization.AtPrime W) (M := T)
      Ideal.Quotient.mk_surjective).symm
end LocalizeQuotientStages
end GroundTheory.Heights₂.Heights
