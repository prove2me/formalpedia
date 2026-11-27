-- Prove2me | solution 1 for PositivityTheory.Lit1.PTN.contAction_twDual_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:18:59.503914+00:00
-- url     : https://prove2.me/submissions/d3b6c838-442f-4e7f-9863-2fc1972e5e52

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsDefs
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PfContActionTwDualC
import Theorems.Thm_GlobalTheory_Published_PoitouTate_continuous_cycMod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open PositivityTheory PositivityTheory.Lit1 PositivityTheory.Lit1.PTN
namespace PositivityTheory.Lit1.PTN
theorem _root_.solution {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
    (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hρ : ContAction ρ) : ContAction (twDual μ ρ) := by
  have hμc : Continuous μ := by
    have hq : Topology.IsQuotientMap (toGS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) :=
      QuotientGroup.isQuotientMap_mk _
    rw [hq.continuous_iff]
    have h2 : (⇑μ ∘ ⇑(toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))))) = ⇑(cycMod F Ω l r) := by
      rw [← hμ]
      rfl
    rw [h2]
    exact GlobalTheory.Published.PoitouTate.continuous_cycMod
  have hρ' : Continuous fun p : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) × M => ρ p.1 p.2 := hρ
  haveI : Fintype M := Fintype.ofFinite M
  show Continuous fun p : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) × TDual (ZMod (l ^ r)) M =>
    twDual μ ρ p.1 p.2
  rw [continuous_prod_of_discrete_right]
  intro φ
  refine continuous_discrete_rng.mpr ?_
  intro ψ
  have hset : (fun g => (twDual μ ρ g) φ) ⁻¹' {ψ} =
      ⋂ m : M, (fun g : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) =>
        ((μ g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * φ (ρ g⁻¹ m)) ⁻¹' {ψ m} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
    constructor
    · rintro h m
      rw [← h, twDual_apply]
    · intro h
      apply TDual.ext
      intro m
      rw [twDual_apply]
      exact h m
  rw [hset]
  refine isOpen_iInter_of_finite fun m => ?_
  have h1 : Continuous fun g : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) =>
      ((μ g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) :=
    Units.continuous_val.comp hμc
  have h2 : Continuous fun g : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) => ρ g⁻¹ m :=
    hρ'.comp (continuous_inv.prodMk continuous_const)
  have h3 : Continuous fun g : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) => φ (ρ g⁻¹ m) :=
    continuous_of_discreteTopology.comp h2
  exact (isOpen_discrete _).preimage (h1.mul h3)
end PositivityTheory.Lit1.PTN
