-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_of_locPrincipal_47d661a47a8e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:52:28.749618+00:00
-- url     : https://prove2.me/submissions/f95ec044-3c57-4b77-adb5-1359e1e223b5

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartierAtOfLocallyPrincipal

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
theorem _root_.solution : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : X.IdealSheafData)
    (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1)),
    LocPrincipal (Z.ideal U) q.asIdeal → CartAt Z (U.2.fromSpec q) := by
  intro X _ Z U q h
  obtain ⟨t, f, ht, hfI, hf0, hg⟩ := h
  have hx : U.2.fromSpec q ∈ X.basicOpen t := by
    have h1 : q ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen t := by
      rw [U.2.fromSpec_preimage_basicOpen]
      exact ht
    exact h1
  have hxU : U.2.fromSpec q ∈ U.1 := X.basicOpen_le t hx
  have inst := U.2.isLocalization_basicOpen t
  let ρ : Γ(X, U.1) →+* Γ(X, X.basicOpen t) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom
  have hu : IsUnit (ρ t) :=
    IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen t)) t
  have hZ : Z.ideal (X.affineBasicOpen t) = Ideal.map ρ (Z.ideal U) :=
    (Z.map_ideal_basicOpen U t).symm
  have hne : Nonempty (X.basicOpen t : X.Opens) := ⟨⟨_, hx⟩⟩
  have hρf : ρ f ≠ 0 := by
    intro h0
    apply hf0
    apply germ_injective_of_isIntegral X (U := U.1) (U.2.fromSpec q) hxU
    have h2 := congrArg (X.presheaf.germ (X.basicOpen t) (U.2.fromSpec q) hx).hom h0
    rw [map_zero] at h2 ⊢
    rw [← h2]
    simp [ρ]
  have hnz : ρ f ∈ nonZeroDivisors Γ(X, X.basicOpen t) := mem_nonZeroDivisors_of_ne_zero hρf
  suffices hspan : Ideal.map ρ (Z.ideal U) = Ideal.span {ρ f} from
    ⟨X.affineBasicOpen t, ρ f, hx, hnz, hZ.trans hspan⟩
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro g hgI
    obtain ⟨n, hn⟩ := hg g hgI
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    obtain ⟨u, hu'⟩ := hu.pow n
    refine ⟨(↑u⁻¹ : Γ(X, X.basicOpen t)) * ρ c, ?_⟩
    have h3 : ρ c * ρ f = ρ t ^ n * ρ g := by
      rw [← map_mul, hc, map_mul, map_pow]
    rw [mul_assoc, h3, ← hu', Units.inv_mul_cancel_left]
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem ρ hfI
end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
