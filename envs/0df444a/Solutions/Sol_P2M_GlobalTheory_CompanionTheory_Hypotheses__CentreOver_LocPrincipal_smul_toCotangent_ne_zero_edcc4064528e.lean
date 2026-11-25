-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_LocPrincipal_smul_toCotangent_ne_zero_edcc4064528e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:29:44.116941+00:00
-- url     : https://prove2.me/submissions/69805aef-ee8f-49fa-bc4f-1028f4ef6dd0

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ConormalRankOneOfLocallyPrincipal
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_LocPrincipal_exists_pow_mul_sq_66e694ab0060

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
namespace LocPrincipal
theorem _root_.solution {A : Type} [CommRing A] [IsDomain A] {I p : Ideal A}
    [p.IsPrime] (hIp : I ≤ p) {t f : A} (ht : t ∉ p) (hf : f ∈ I) (hf0 : f ≠ 0)
    (h : ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f}) {s : A} (hs : s ∉ p) :
    s • I.toCotangent ⟨f, hf⟩ ≠ 0 := by
  intro h0
  rw [← map_smul I.toCotangent s ⟨f, hf⟩, Ideal.toCotangent_eq_zero] at h0
  have h0' : s * f ∈ I ^ 2 := by simpa [smul_eq_mul] using h0
  obtain ⟨N, c, hc⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.LocPrincipal.exists_pow_mul_sq h h0'
  have hcancel : t ^ N * s = c * f := by
    apply mul_right_cancel₀ hf0
    calc t ^ N * s * f = t ^ N * (s * f) := by ring
      _ = c * (f * f) := hc
      _ = c * f * f := by ring
  have hmem : t ^ N * s ∈ p := by
    rw [hcancel]
    exact hIp (I.mul_mem_left c hf)
  rcases Ideal.IsPrime.mem_or_mem ‹p.IsPrime› hmem with h1 | h1
  · exact ht (Ideal.IsPrime.mem_of_pow_mem ‹p.IsPrime› N h1)
  · exact hs h1
end LocPrincipal
end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
