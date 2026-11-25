-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_exists_generator_of_rankAtStalk_eq_one_fad9a8a39d3b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:52:35.276798+00:00
-- url     : https://prove2.me/submissions/058dcbc9-ab20-4516-8132-97b86476bcb8

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocallyPrincipalOfConormalRankOne

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
theorem _root_.solution {B M : Type*} [CommRing B] [AddCommGroup M]
    [Module B M] [Module.Finite B M] [Module.Projective B M] (P : PrimeSpectrum B)
    (h : Module.rankAtStalk M P = 1) :
    ∃ m : M, ∀ x : M, ∃ s : B, s ∉ P.asIdeal ∧ ∃ b : B, s • x = b • m := by
  haveI : Module.Flat B M := Module.Flat.of_projective
  let S := P.asIdeal.primeCompl
  let f := LocalizedModule.mkLinearMap S M
  haveI : Module.Free (Localization.AtPrime P.asIdeal) (LocalizedModule S M) :=
    Module.mem_freeLocus.mp (by simp only [Module.freeLocus_eq_univ, Set.mem_univ])
  haveI : Module.Finite (Localization.AtPrime P.asIdeal) (LocalizedModule S M) :=
    Module.Finite.of_isLocalizedModule S f
  let e := Module.finBasisOfFinrankEq (Localization.AtPrime P.asIdeal) (LocalizedModule S M) h
  obtain ⟨⟨m, s0⟩, hm⟩ := IsLocalizedModule.surj S f (e 0)
  refine ⟨m, fun x => ?_⟩
  have hx : f x = (e.repr (f x) 0) • e 0 := by
    have hsum := e.sum_repr (f x)
    rw [Fin.sum_univ_one] at hsum
    exact hsum.symm
  obtain ⟨⟨a, u⟩, hu⟩ := IsLocalization.surj S (e.repr (f x) 0)
  have key : f (((u : B) * (s0 : B)) • x) = f (a • m) := by
    rw [map_smul, map_smul, hx, ← hm, Submonoid.smul_def,
      ← algebraMap_smul (Localization.AtPrime P.asIdeal) ((u : B) * (s0 : B)),
      ← algebraMap_smul (Localization.AtPrime P.asIdeal) a,
      ← algebraMap_smul (Localization.AtPrime P.asIdeal) (s0 : B)]
    simp only [smul_smul]
    congr 1
    rw [map_mul, ← hu]
    ring
  obtain ⟨v, hv⟩ := (IsLocalizedModule.eq_iff_exists S f).mp key
  refine ⟨(v : B) * ((u : B) * (s0 : B)), (v * (u * s0)).2, (v : B) * a, ?_⟩
  first
    | (rw [mul_smul (v : B) ((u : B) * (s0 : B)) x, mul_smul (v : B) a m]; exact hv)
    | simpa only [Submonoid.smul_def, mul_smul] using hv
end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
