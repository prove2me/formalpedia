-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.stonean_clopens_recover_space
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T23:39:58.75018+00:00
-- url     : https://prove2.me/submissions/b222916c-53a4-4ffa-8551-8926e9f225e5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_stone_topology_properties
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Sets.Closeds
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace


open scoped Topology

universe u v

/-- Lemma 3.8; de Groote, Observables I, PDF p./pp. 72.
-/
theorem solution {M : Type u} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ExtremallyDisconnected M] :
    ∃ h : StoneSpectrum (Clopens M) ≃ₜ M,
      ∀ B, (⋂ U : {U : Clopens M // U ∈ B.val}, (U.val : Set M)) = {h B} := by
  classical
  have hp (x : M) : IsQuasipoint {U : Clopens M | x ∈ U} := by
    refine ⟨⟨⟨⊤,by change x ∈ (Set.univ : Set M); trivial⟩,by change x ∉ (∅ : Set M); simp,?_⟩,?_⟩
    · intro U hU V hV
      exact ⟨U ⊓ V,⟨hU,hV⟩,inf_le_left,inf_le_right⟩
    · intro C hC hPC
      apply Set.Subset.antisymm _ hPC
      intro U hU
      by_contra hx
      have hc : Uᶜ ∈ C := hPC hx
      obtain ⟨V,hV,hVU,hVc⟩ := hC.2.2 U hU Uᶜ hc
      have hz : V = ⊥ := by
        apply le_bot_iff.mp
        simpa using (le_inf hVU hVc)
      exact hC.2.1 (hz ▸ hV)
  let g : M → StoneSpectrum (Clopens M) := fun x => ⟨{U | x ∈ U},hp x⟩
  have hg : Continuous g := by
    change @Continuous _ _ _ (TopologicalSpace.generateFrom (Set.range (stoneBasic : Clopens M → Set (StoneSpectrum (Clopens M))))) g
    apply continuous_generateFrom_iff.mpr
    rintro _ ⟨U,rfl⟩
    exact U.isOpen
  have hi : Function.Injective g := by
    intro x y hxy
    by_contra hne
    obtain ⟨V,hV,hxV,hVsub⟩ := compact_exists_isClopen_in_isOpen
      (isClosed_singleton.isOpen_compl : IsOpen ({y}ᶜ : Set M)) (by simpa using hne)
    let U : Clopens M := ⟨V,hV⟩
    have hu : U ∈ (g x).val := hxV
    rw [hxy] at hu
    exact hVsub hu rfl
  have hs : Function.Surjective g := by
    intro B
    letI : Nonempty {U : Clopens M // U ∈ B.val} := by
      obtain ⟨U,hU⟩ := B.property.1.1
      exact ⟨⟨U,hU⟩⟩
    let T := fun U : {U : Clopens M // U ∈ B.val} => (U.val : Set M)
    have hd : Directed (· ⊇ ·) T := by
      intro U V
      obtain ⟨W,hW,hWU,hWV⟩ := B.property.1.2.2 U.val U.property V.val V.property
      exact ⟨⟨W,hW⟩,hWU,hWV⟩
    have hn (U : {U : Clopens M // U ∈ B.val}) : (T U).Nonempty := by
      apply Set.nonempty_iff_ne_empty.mpr
      intro hz
      have hu : U.val = ⊥ := SetLike.coe_injective hz
      exact B.property.1.2.1 (hu ▸ U.property)
    obtain ⟨x,hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      T hd hn (fun U => U.val.isClosed.isCompact) (fun U => U.val.isClosed)
    refine ⟨x,Subtype.ext ?_⟩
    apply B.property.2 (g x).val (g x).property.1
    intro U hU
    exact Set.mem_iInter.mp hx ⟨U,hU⟩
  let e := Equiv.ofBijective g ⟨hi,hs⟩
  letI : T2Space (StoneSpectrum (Clopens M)) :=
    (stone_topology_properties (L := Clopens M)).2.2.2.2.2.2.1
  let E : M ≃ₜ StoneSpectrum (Clopens M) := e.toHomeomorphOfContinuousClosed hg hg.isClosedMap
  refine ⟨E.symm,?_⟩
  intro B
  ext x
  change (x ∈ ⋂ U : {U : Clopens M // U ∈ B.val}, (U.val : Set M)) ↔ x = e.symm B
  have hm : (x ∈ ⋂ U : {U : Clopens M // U ∈ B.val}, (U.val : Set M)) ↔ g x = B := by
    constructor
    · intro hx
      apply Subtype.ext
      apply B.property.2 (g x).val (g x).property.1
      intro U hU
      exact Set.mem_iInter.mp hx ⟨U,hU⟩
    · intro he
      rw [← he]
      apply Set.mem_iInter.mpr
      intro U
      exact U.property
  rw [hm]
  constructor
  · intro he
    have hh := congrArg e.symm he
    change e.symm (e x) = e.symm B at hh
    rw [Equiv.symm_apply_apply] at hh
    exact hh
  · intro he
    subst x
    exact e.apply_symm_apply B
