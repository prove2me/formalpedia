-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_exists_gen_of_map_eq_span_8fb85a512b0b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:52:33.626806+00:00
-- url     : https://prove2.me/submissions/e7793337-f0b4-40e2-9cf4-d117db5c9c21

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocallyPrincipalOfCartierAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (t : A)
    [IsLocalization.Away t B] (I : Ideal A) (b : B) (hb : b ≠ 0)
    (hI : I.map (algebraMap A B) = Ideal.span {b}) :
    ∃ f ∈ I, f ≠ 0 ∧ ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f} := by
  have hbI : b ∈ I.map (algebraMap A B) := by
    rw [hI]
    exact Ideal.mem_span_singleton_self b
  obtain ⟨⟨f, s⟩, hf⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers t) B).mp hbI
  refine ⟨f, f.2, ?_, ?_⟩
  · intro h0
    apply hb
    rw [h0, map_zero] at hf
    exact ((IsLocalization.map_units B s).mul_left_eq_zero).mp hf
  · intro g hg
    have hg' : algebraMap A B g ∈ Ideal.span {b} := by
      rw [← hI]
      exact Ideal.mem_map_of_mem _ hg
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hg'
    obtain ⟨⟨a, u⟩, hu⟩ := IsLocalization.surj (Submonoid.powers t) c
    have key : algebraMap A B ((u : A) * (s : A) * g) = algebraMap A B (a * (f : A)) := by
      rw [map_mul, map_mul, map_mul, ← hc, ← hu, ← hf]
      ring
    obtain ⟨e, he⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers t) B).mp key
    obtain ⟨l, hl⟩ := (Submonoid.mem_powers_iff _ _).mp e.2
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp u.2
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    rw [← hl, ← hj, ← hk] at he
    refine ⟨l + j + k, Ideal.mem_span_singleton'.mpr ⟨t ^ l * a, ?_⟩⟩
    rw [pow_add, pow_add]
    linear_combination -he
end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
