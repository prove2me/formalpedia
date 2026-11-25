-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_LocPrincipal_exists_pow_smul_eq_34d381c8a314
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:52:44.568465+00:00
-- url     : https://prove2.me/submissions/26ef782e-3154-4b71-be38-afb02918cd3d

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ConormalRankOneOfLocallyPrincipal

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
theorem _root_.solution {A : Type} [CommRing A] {I : Ideal A} {t f : A}
    (hf : f ∈ I) (h : ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f}) (m : I.Cotangent) :
    ∃ (n : ℕ) (c : A), t ^ n • m = c • I.toCotangent ⟨f, hf⟩ := by
  obtain ⟨g, rfl⟩ := I.toCotangent_surjective m
  obtain ⟨n, hn⟩ := h g g.2
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hn
  refine ⟨n, c, ?_⟩
  rw [← map_smul I.toCotangent (t ^ n) g, ← map_smul I.toCotangent c ⟨f, hf⟩]
  congr 1
  ext
  simp [smul_eq_mul, hc]
end LocPrincipal
end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
