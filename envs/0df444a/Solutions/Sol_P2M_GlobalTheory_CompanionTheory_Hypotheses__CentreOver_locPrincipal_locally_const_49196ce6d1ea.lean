-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_locPrincipal_locally_const_49196ce6d1ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:55.064101+00:00
-- url     : https://prove2.me/submissions/e507e235-d072-4197-a7c0-3aa8defe9222

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ConormalFiniteProjectiveOfSmoothStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocallyPrincipalOfConormalRankOneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ConormalRankOneOfLocallyPrincipalStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocallyPrincipalOfCartierAtStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartierAtOfLocallyPrincipalStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExistsSmoothAffinePresentationPairStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsClosedCartierLocusSupport
import Theorems.Thm_GlobalTheory_T_conormal_finite_projective_of_smooth
import Theorems.Thm_GlobalTheory_T_conormal_rank_one_of_locally_principal
import Theorems.Thm_GlobalTheory_T_locally_principal_of_conormal_rank_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
theorem _root_.solution {k A : Type} [Field k] [CommRing A] [IsDomain A] (φ : k →+* A) (I : Ideal A)
    (hφ : φ.Smooth) (hI : ((Ideal.Quotient.mk I).comp φ).Smooth) (p : PrimeSpectrum A)
    (hp : I ≤ p.asIdeal) :
    ∃ s, s ∉ p.asIdeal ∧ ∀ q : PrimeSpectrum A, s ∉ q.asIdeal → I ≤ q.asIdeal →
      (LocPrincipal I q.asIdeal ↔ LocPrincipal I p.asIdeal) := by
  obtain ⟨hfin, hproj⟩ := GlobalTheory.T.conormal_finite_projective_of_smooth φ I hφ hI
  have hnoeth : IsNoetherianRing A := by
    algebraize [φ]
    have : Algebra.FiniteType k A := inferInstance
    exact Algebra.FiniteType.isNoetherianRing k A
  have := Module.finitePresentation_of_projective (A ⧸ I) I.Cotangent
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  have hce := PrimeSpectrum.isClosedEmbedding_comap_of_surjective (A ⧸ I) (Ideal.Quotient.mk I) hsurj
  have hrange : ∀ q : PrimeSpectrum A, I ≤ q.asIdeal →
      ∃ Q : PrimeSpectrum (A ⧸ I), PrimeSpectrum.comap (Ideal.Quotient.mk I) Q = q := by
    intro q hq
    have : q ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := by
      rw [_root_.range_comap_of_surjective _ _ hsurj, Ideal.mk_ker]
      exact hq
    exact this
  obtain ⟨P0, hP0⟩ := hrange p hp
  have hlc : IsLocallyConstant (Module.rankAtStalk (R := A ⧸ I) I.Cotangent) :=
    Module.isLocallyConstant_rankAtStalk
  have hO := hlc.isOpen_fiber (Module.rankAtStalk (R := A ⧸ I) I.Cotangent P0)
  obtain ⟨W, hW, hWO⟩ := hce.isInducing.isOpen_iff.1 hO
  have hpW : p ∈ W := by
    have : P0 ∈ PrimeSpectrum.comap (Ideal.Quotient.mk I) ⁻¹' W := by rw [hWO]; rfl
    rwa [Set.mem_preimage, hP0] at this
  obtain ⟨_, ⟨s, rfl⟩, hps, hsW⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpW hW
  refine ⟨s, hps, fun q hs hq => ?_⟩
  obtain ⟨Q, hQ⟩ := hrange q hq
  have hQO : Module.rankAtStalk (R := A ⧸ I) I.Cotangent Q = Module.rankAtStalk (R := A ⧸ I) I.Cotangent P0 := by
    have : Q ∈ PrimeSpectrum.comap (Ideal.Quotient.mk I) ⁻¹' W := by
      rw [Set.mem_preimage, hQ]; exact hsW hs
    rw [hWO] at this
    exact this
  have e : ∀ R : PrimeSpectrum (A ⧸ I), LocPrincipal I (PrimeSpectrum.comap (Ideal.Quotient.mk I) R).asIdeal ↔ Module.rankAtStalk (R := A ⧸ I) I.Cotangent R = 1 :=
    fun R => ⟨GlobalTheory.T.conormal_rank_one_of_locally_principal I R, GlobalTheory.T.locally_principal_of_conormal_rank_one I R⟩
  rw [← hQ, ← hP0, e, e, hQO]
end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
