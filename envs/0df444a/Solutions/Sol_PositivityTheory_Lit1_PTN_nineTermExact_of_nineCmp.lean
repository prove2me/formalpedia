-- Prove2me | solution 1 for PositivityTheory.Lit1.PTN.nineTermExact_of_nineCmp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:40:22.55443+00:00
-- url     : https://prove2.me/submissions/2c6c3213-6052-4af0-bf0a-145ce753e1e3

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsDefs
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsTransfer
import Theorems.Thm_PositivityTheory_Lit1_PTN_exact_of_transfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion
open PositivityTheory PositivityTheory.Lit1 PositivityTheory.Lit1.PTN
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
  (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
  (hρ : ContAction ρ)
namespace PositivityTheory.Lit1.PTN
theorem _root_.solution
    (h : NineCmp (loc0 S Av ρ) (tr0 S Av μ j ρ) (loc1 S Av ρ) (tr1 S Av μ j ρ hρ)
      (loc2 S Av ρ) (tr2 S Av μ j ρ)) : NineTermExact S Av μ j ρ hρ := by
  obtain ⟨B0, B1, B2, B3, B4, B5, B6, B7, BetaSesquilinearity, g0, g1, g2, g3, g4, g5, g6, g7,
    e0, e1, e2, e3, e4, e5, e6, e7, e8, u, h0, h1, h3, h4, h6, h7,
    i0, x01, x12, x23, x34, x45, x56, x67, s7⟩ := h
  have k2 : ∀ a, g2 (e2 a) = (1 : (ZMod (l ^ r))ˣ) • e3 ((e3.symm.toLinearMap ∘ₗ g2 ∘ₗ e2.toLinearMap) a) := by
    intro a; rw [one_smul]; exact (e3.apply_symm_apply _).symm
  have k5 : ∀ a, g5 (e5 a) = (1 : (ZMod (l ^ r))ˣ) • e6 ((e6.symm.toLinearMap ∘ₗ g5 ∘ₗ e5.toLinearMap) a) := by
    intro a; rw [one_smul]; exact (e6.apply_symm_apply _).symm
  refine ⟨e3.symm.toLinearMap ∘ₗ g2 ∘ₗ e2.toLinearMap, e6.symm.toLinearMap ∘ₗ g5 ∘ₗ e5.toLinearMap,
    ?_, exact_of_transfer _ _ _ _ e0 e1 e2 _ _ h0 h1 x01,
    exact_of_transfer _ _ _ _ e1 e2 e3 _ _ h1 k2 x12,
    exact_of_transfer _ _ _ _ e2 e3 e4 _ _ k2 h3 x23,
    exact_of_transfer _ _ _ _ e3 e4 e5 _ _ h3 h4 x34,
    exact_of_transfer _ _ _ _ e4 e5 e6 _ _ h4 k5 x45,
    exact_of_transfer _ _ _ _ e5 e6 e7 _ _ k5 h6 x56,
    exact_of_transfer _ _ _ _ e6 e7 e8 _ _ h6 h7 x67, ?_⟩
  · intro a b hab
    apply e0.injective
    apply i0
    rw [h0, h0, hab]
  · intro y
    obtain ⟨b, hb⟩ := s7 (e8 y)
    refine ⟨((u 5 : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) • e7.symm b, e8.injective ?_⟩
    have := h7 (e7.symm b)
    rw [LinearEquiv.apply_symm_apply, hb] at this
    rw [map_smul, map_smul, this, Units.smul_def]
end PositivityTheory.Lit1.PTN
