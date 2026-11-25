-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_rankAtStalk_cotangent_eq_one_a658a82d8682
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:38:11.467265+00:00
-- url     : https://prove2.me/submissions/42abcda4-3213-48de-816a-a61e46258865

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ConormalRankOneOfLocallyPrincipal
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_LocPrincipal_smul_toCotangent_ne_zero_edcc4064528e
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_LocPrincipal_exists_pow_smul_eq_34d381c8a314

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
theorem _root_.solution {A : Type} [CommRing A] [IsDomain A] (I : Ideal A)
    [Module.Finite (A ⧸ I) I.Cotangent] [Module.Projective (A ⧸ I) I.Cotangent]
    (P : PrimeSpectrum (A ⧸ I))
    (hP : LocPrincipal I (P.asIdeal.comap (Ideal.Quotient.mk I))) :
    Module.rankAtStalk I.Cotangent P = 1 := by
  obtain ⟨t, f, ht, hf, hf0, h⟩ := hP
  have htP : Ideal.Quotient.mk I t ∉ P.asIdeal := fun H => ht (Ideal.mem_comap.mpr H)
  have hIq : I ≤ P.asIdeal.comap (Ideal.Quotient.mk I) := fun g hg => by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hg]
    exact zero_mem _
  have hsmul : ∀ (a : A) (m : I.Cotangent), Ideal.Quotient.mk I a • m = a • m := fun a m => by
    rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  have hspan : Submodule.span (Localization.AtPrime P.asIdeal)
      {LocalizedModule.mk (I.toCotangent ⟨f, hf⟩) (1 : P.asIdeal.primeCompl)} = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    induction y using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨n, c, hc⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.LocPrincipal.exists_pow_smul_eq hf h m
      have htn : (Ideal.Quotient.mk I t) ^ n ∈ P.asIdeal.primeCompl :=
        Ideal.mem_primeCompl_iff.mpr fun H => htP (Ideal.IsPrime.mem_of_pow_mem P.isPrime n H)
      have key : Ideal.Quotient.mk I c • I.toCotangent ⟨f, hf⟩ =
          (⟨_, htn⟩ : P.asIdeal.primeCompl) • m := by
        rw [Submonoid.mk_smul, hsmul, ← map_pow, hsmul]
        exact hc.symm
      rw [Submodule.mem_span_singleton]
      refine ⟨Localization.mk (Ideal.Quotient.mk I c) (⟨_, htn⟩ * s), ?_⟩
      rw [LocalizedModule.mk_smul_mk, key, mul_one, LocalizedModule.mk_cancel_common_left]
  have hx : LocalizedModule.mk (I.toCotangent ⟨f, hf⟩) (1 : P.asIdeal.primeCompl) ≠ 0 := by
    intro H
    rw [← LocalizedModule.zero_mk (1 : P.asIdeal.primeCompl), LocalizedModule.mk_eq] at H
    obtain ⟨⟨u, hu⟩, hu0⟩ := H
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective u
    simp only [one_smul, smul_zero, Submonoid.mk_smul] at hu0
    rw [hsmul] at hu0
    exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.LocPrincipal.smul_toCotangent_ne_zero hIq ht hf hf0 h
      (fun hs => Ideal.mem_primeCompl_iff.mp hu (Ideal.mem_comap.mp hs)) hu0
  have hfree : Module.Free (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl I.Cotangent) := by
    haveI : Module.Flat (A ⧸ I) I.Cotangent := Module.Flat.of_projective
    have hmem : P ∈ Module.freeLocus (A ⧸ I) I.Cotangent := by
      rw [Module.freeLocus_eq_univ]
      trivial
    exact Module.mem_freeLocus.mp hmem
  haveI : Module.Finite (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl I.Cotangent) :=
    Module.Finite.of_fg_top ⟨{LocalizedModule.mk (I.toCotangent ⟨f, hf⟩) 1}, by
      rw [Finset.coe_singleton]
      exact hspan⟩
  haveI := nontrivial_of_ne _ _ hx
  have hle : Module.finrank (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl I.Cotangent) ≤ 1 := by
    have := finrank_le_of_span_eq_top (R := Localization.AtPrime P.asIdeal)
      (v := fun _ : Unit => LocalizedModule.mk (I.toCotangent ⟨f, hf⟩)
        (1 : P.asIdeal.primeCompl)) (by rw [Set.range_const]; exact hspan)
    simpa using this
  have hpos : 0 < Module.finrank (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl I.Cotangent) :=
    (Module.finrank_pos_iff_of_free _ _).mpr inferInstance
  show Module.finrank (Localization.AtPrime P.asIdeal)
    (LocalizedModule P.asIdeal.primeCompl I.Cotangent) = 1
  omega
end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
