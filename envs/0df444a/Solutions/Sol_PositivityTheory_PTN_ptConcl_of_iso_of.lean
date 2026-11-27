-- Prove2me | solution 1 for PositivityTheory.PTN.ptConcl_of_iso_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:21:28.692553+00:00
-- url     : https://prove2.me/submissions/592a37f5-6d03-47e2-b6b9-d1ef3812c4c1

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaloisGroupTransportIsomorphismStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RingIsomorphismTransportsPlacesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TotallyComplexOfRingEquivStatement
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsHyp
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RingEquivTransportsDecompositionStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InertiaQuotientTransportStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RingEquivCyclotomicCharacterStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RingEquivTransportsInertiaStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RingEquivTransportsResidueStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateSequenceTransportStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TateShafarevichTransportStatement
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtConclOfIsoOf
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_NineTransfer_piE_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_nineTermExact_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_shaDual_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_subgroupIso_coe
import Theorems.Thm_GlobalTheory_T_galois_group_transport_isomorphism
import Theorems.Thm_GlobalTheory_T_galois_quotient_equiv_of_matching_places
import Theorems.Thm_GlobalTheory_T_poitou_tate_sequence_transport
import Theorems.Thm_GlobalTheory_T_ring_equiv_cyclotomic_character
import Theorems.Thm_GlobalTheory_T_ring_equiv_transports_decomposition
import Theorems.Thm_GlobalTheory_T_ring_equiv_transports_inertia
import Theorems.Thm_GlobalTheory_T_ring_equiv_transports_residue
import Theorems.Thm_GlobalTheory_T_ring_isomorphism_transports_places
import Theorems.Thm_GlobalTheory_T_tate_shafarevich_transport
import Theorems.Thm_GlobalTheory_T_totally_complex_of_ring_equiv
import Theorems.Thm_P2M_ReciprocityTheory_Gal_ContAction_comp__44f330b68efd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.PTIso.NineTransfer.piE_apply
attribute [local simp] GlobalTheory.CompanionTheory.PTIso.subgroupIso_coe



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
open PositivityTheory PositivityTheory.PTN
namespace PositivityTheory.PTN
theorem _root_.solution (hL : PositivityTheory.PTN.LocHyp) : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → PTConclAt F' Ω' → PTConclAt F Ω := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE hPT
  intro l _ r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.galois_group_transport_isomorphism F Ω F' Ω' e E hE
  obtain ⟨eO, eV, heO, hV, hV2, hN⟩ := GlobalTheory.T.ring_isomorphism_transports_places F F' e
  have hloc := hL F Ω F' Ω' e E hE Φ hΦ
  have hpl := GlobalTheory.T.ring_equiv_transports_decomposition F Ω F' Ω' e E hE eO eV heO hV
  have hcyc := GlobalTheory.T.ring_equiv_cyclotomic_character F Ω F' Ω' e E hE Φ hΦ l r
  obtain ⟨inv', hinv'⟩ := GlobalTheory.T.ring_equiv_transports_inertia F Ω F' Ω' e E hE Φ hΦ
    (fun A A' hA σ => (hloc A A' hA σ).1) l r hcyc inv

  let S' : Finset (HeightOneSpectrum (𝓞 F')) := S.map eV.toEmbedding
  have hSS : ∀ v, v ∈ (S : Set (HeightOneSpectrum (𝓞 F))) ↔
      eV v ∈ (S' : Set (HeightOneSpectrum (𝓞 F'))) := by
    intro v; simp [S']
  let eI : S ≃ S' := Equiv.subtypeEquiv eV (fun v => by simp [S'])
  have heI : ∀ v : S, (eI v : HeightOneSpectrum (𝓞 F')) = eV v := fun _ => rfl
  let Av' : S' → ValuationSubring Ω' := fun v' => (Av (eI.symm v')).comap E.symm.toRingHom
  have hAv'' : ∀ (v : S) (x : Ω), E x ∈ Av' (eI v) ↔ x ∈ Av v := by
    intro v x
    simp [Av', ValuationSubring.mem_comap]
  have hPl' : ∀ v' : S', IsPlaceOver (Av' v') v'.1 := by
    intro v'
    obtain ⟨v, rfl⟩ := eI.surjective v'
    exact (hpl _ _ (hAv'' v) v.1).1 (hAv v)

  obtain ⟨Ψ, hΨ⟩ := GlobalTheory.T.galois_quotient_equiv_of_matching_places F Ω F' Ω' e E hE Φ hΦ eV hpl
    (fun A A' hA σ => (hloc A A' hA σ).2.1) _ _ hSS
  let μ' : GS Ω' (S' : Set (HeightOneSpectrum (𝓞 F'))) →* (ZMod (l ^ r))ˣ :=
    μ.comp (Ψ.symm : GS Ω' (S' : Set (HeightOneSpectrum (𝓞 F'))) →* _)
  have hμ' : μ'.comp (toGS Ω' _) = cycMod F' Ω' l r := by
    ext1 τ
    obtain ⟨σ, rfl⟩ := Φ.surjective τ
    have h1 : Ψ.symm (toGS Ω' _ (Φ σ)) = toGS Ω _ σ := by rw [← hΨ]; simp
    have h2 : μ (toGS Ω _ σ) = cycMod F Ω l r σ := DFunLike.congr_fun hμ σ
    show μ (Ψ.symm (toGS Ω' _ (Φ σ))) = _
    rw [h1, h2, hcyc]
  let ρ' : Representation (ZMod (l ^ r)) (GS Ω' (S' : Set (HeightOneSpectrum (𝓞 F')))) M :=
    ρ.comp (Ψ.symm : GS Ω' (S' : Set (HeightOneSpectrum (𝓞 F'))) →* _)
  have hρ' : ContAction ρ' := hρ.comp' Ψ.symm.continuous

  have hl' : l ≠ 2 ∨ IsTotallyComplex F' := hl.imp id (GlobalTheory.T.totally_complex_of_ring_equiv F F' e)
  have hζ' : IsPrimitiveRoot (E ζ) (l ^ r) := hζ.map_of_injective E.injective
  have hnorm' : InvNormalised (E ζ) inv' := by
    intro A' v' hP
    obtain ⟨v, rfl⟩ := eV.surjective v'
    let A : ValuationSubring Ω := A'.comap E.toRingHom
    have hA : ∀ x, E x ∈ A' ↔ x ∈ A := fun x => by simp [A, ValuationSubring.mem_comap]
    have hP0 : IsPlaceOver A v := (hpl A A' hA v).2 hP
    refine ⟨(hinv' A A' hA).1 (hinv A v hP0).1, ?_⟩
    exact GlobalTheory.T.ring_equiv_transports_residue F Ω F' Ω' e E hE Φ hΦ eO eV heO hV hV2 hN l r hcyc A A' hA (hloc A A' hA) ζ v
      (inv A) (inv' A') (hinv' A A' hA).2 (hinv A v hP0).2
  have hS' : ContainsAbove S' l := by
    intro v' hv'
    obtain ⟨v, rfl⟩ := eV.surjective v'
    have : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal := by
      rw [hV, map_natCast]; exact hv'
    exact Finset.mem_map_of_mem _ (hS v this)
  obtain ⟨h9, hsha⟩ := hPT l r hl' hr (E ζ) hζ' inv' hnorm' S' hS' Av' hPl' μ' hμ' M ρ' hρ'

  let eD : ∀ v : S, Dec (F := F) (Av v) ≃ₜ* Dec (F := F') (Av' (eI v)) := fun v =>
    subgroupIso Φ _ _ (fun σ => (hloc _ _ (hAv'' v) σ).1)
  have hcomp : ∀ (v : S) (d : Dec (F := F) (Av v)),
      locFam S' Av' (eI v) (eD v d) = Ψ (locFam S Av v d) := by
    intro v d
    exact (hΨ (d : G F Ω)).symm
  have hχ : ∀ g, μ' (Ψ g) = μ g := fun g => by simp [μ']
  have hρc : ∀ g m, ρ' (Ψ g) m = ρ g m := fun g m => by simp [ρ']
  refine ⟨?_, ?_⟩
  · refine (nineTermExact_iff S Av μ _ ρ hρ).2 ?_
    refine GlobalTheory.T.poitou_tate_sequence_transport (locFam S Av) (continuous_locFam S Av) (locFam S' Av') (continuous_locFam S' Av')
      μ μ' ρ ρ' Ψ eI eD hcomp hχ hρc _ _ hρ hρ' ?_ ((nineTermExact_iff S' Av' μ' _ ρ' hρ').1 h9)
    intro v z z' hz
    refine (hinv' _ _ (hAv'' v)).2 (cocycles2Map _ _ LinearMap.id continuous_id (locFam_apply_eq S Av μ hμ v) z)
      (cocycles2Map _ _ LinearMap.id continuous_id (locFam_apply_eq S' Av' μ' hμ' (eI v)) z') ?_
    intro g h g' h' hg hh
    have e1 : g' = eD v g := Subtype.ext hg
    have e2 : h' = eD v h := Subtype.ext hh
    subst e1 e2
    exact hz g h
  · exact (shaDual_iff S Av μ ρ).2 (GlobalTheory.T.tate_shafarevich_transport (locFam S Av) (continuous_locFam S Av) (locFam S' Av')
      (continuous_locFam S' Av') μ μ' ρ ρ' Ψ eI eD hcomp hχ hρc ((shaDual_iff S' Av' μ' ρ').1 hsha))
end PositivityTheory.PTN
