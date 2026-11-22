-- Prove2me | solution 1 for card_restrict_le_sauer_shelah_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:39:02.864136+00:00
-- url     : https://prove2.me/submissions/4f58ba87-dae5-40e0-a879-e9a160e4c13c

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Data
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Ordinal
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Bayesian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Bridge
section
@[expose] public section
universe u v
private theorem funcToSubset_injective {X : Type u} (S : Finset X) :
    Function.Injective (fun (f : ↥S → Bool) => Finset.univ.filter (fun x => f x = true)) := by
  intro f g h
  funext x
  have hmem := Finset.ext_iff.mp h x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  cases hf : f x <;> cases hg : g x <;> simp_all
private theorem restrict_shatters_lift {X : Type u} [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) (S : Finset X)
    (T : Finset ↥S)
    (hT : (funcToSubsetFamily S (restrictConceptClass C S)).Shatters T) :
    (conceptClassToFinsetFamily C).Shatters (T.map ⟨Subtype.val, Subtype.val_injective⟩) := by
  -- Need: ∀ t ⊆ T.map val, ∃ u ∈ conceptClassToFinsetFamily C, (T.map val) ∩ u = t
  intro t ht
  -- Pull t back to a subset of T in ↥S
  -- t ⊆ T.map val, so each element of t is Subtype.val of some element of T
  -- Define t' : Finset ↥S as the preimage
  let t' : Finset ↥S := T.filter (fun x => ↑x ∈ t)
  have ht'T : t' ⊆ T := Finset.filter_subset _ _
  -- Use hT to get A ∈ 𝒜 with T ∩ A = t'
  obtain ⟨A, hA, hTA⟩ := hT ht'T
  -- A ∈ funcToSubsetFamily S (restrictConceptClass C S) means
  -- A = univ.filter (fun x => f x = true) for some f ∈ restrictConceptClass C S
  simp only [funcToSubsetFamily, restrictConceptClass, Finset.mem_image] at hA
  obtain ⟨f, ⟨c, hcC, rfl⟩, rfl⟩ := hA
  -- hTA : T ∩ univ.filter (fun x => restrictToFinset c S x = true) = t'
  -- restrictToFinset c S = fun ⟨x, _⟩ => c x, so this is T ∩ {x | c ↑x = true}
  simp only [restrictToFinset] at hTA
  -- Now hTA : T ∩ univ.filter (fun x => c ↑x = true) = t'
  refine ⟨conceptToFinset c, Finset.mem_image.mpr ⟨c, hcC, rfl⟩, ?_⟩
  ext y
  simp only [Finset.mem_inter, Finset.mem_map, Function.Embedding.coeFn_mk,
    conceptToFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  -- Key helper: membership in T ∩ filter ↔ membership in t'
  have mem_iff : ∀ (z : ↥S), z ∈ T ∩ Finset.univ.filter (fun x => c ↑x = true) ↔ z ∈ t' :=
    fun z => Finset.ext_iff.mp hTA z
  constructor
  · -- y ∈ (T.map val) ∩ {x | c x = true} → y ∈ t
    rintro ⟨⟨⟨x, hxS⟩, hxT, rfl⟩, hcx⟩
    have hx_in : (⟨x, hxS⟩ : ↥S) ∈ T ∩ Finset.univ.filter (fun x => c ↑x = true) := by
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hxT, hcx⟩
    have hx_t' := (mem_iff _).mp hx_in
    simp only [t', Finset.mem_filter] at hx_t'
    exact hx_t'.2
  · -- y ∈ t → y ∈ (T.map val) ∩ {x | c x = true}
    intro hyt
    have hyS : y ∈ S := by
      have := ht hyt
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at this
      obtain ⟨⟨_, hxS⟩, _, rfl⟩ := this
      exact hxS
    have hyT : (⟨y, hyS⟩ : ↥S) ∈ T := by
      have := ht hyt
      simp_all
    constructor
    · exact ⟨⟨y, hyS⟩, hyT, rfl⟩
    · have hy_t' : (⟨y, hyS⟩ : ↥S) ∈ t' := by
        simp only [t', Finset.mem_filter]
        exact ⟨hyT, hyt⟩
      have := (mem_iff ⟨y, hyS⟩).mpr hy_t'
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this.2
private theorem vcDim_restrict_le {X : Type u} [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) (S : Finset X) :
    Finset.vcDim (funcToSubsetFamily S (restrictConceptClass C S)) ≤
      Finset.vcDim (conceptClassToFinsetFamily C) := by
  -- vcDim = shatterer.sup card. Need: for each T ∈ 𝒜.shatterer, T.card ≤ vcDim(C_finset)
  simp only [Finset.vcDim]
  apply Finset.sup_le
  intro T hT
  have hTs : (funcToSubsetFamily S (restrictConceptClass C S)).Shatters T :=
    Finset.mem_shatterer.mp hT
  have hLift := restrict_shatters_lift C S T hTs
  have hCard : (T.map ⟨Subtype.val, Subtype.val_injective⟩).card = T.card :=
    Finset.card_map _
  calc T.card = (T.map ⟨Subtype.val, Subtype.val_injective⟩).card := hCard.symm
    _ ≤ Finset.vcDim (conceptClassToFinsetFamily C) := hLift.card_le_vcDim
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution {X : Type u} [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) (S : Finset X)
    (d : ℕ) (hd : Finset.vcDim (conceptClassToFinsetFamily C) = d) :
    (restrictConceptClass C S).card ≤
      ∑ i ∈ Finset.range (d + 1), Nat.choose S.card i := by
  -- Let 𝒜 = funcToSubsetFamily S (restrictConceptClass C S) : Finset (Finset ↥S)
  set 𝒜 := funcToSubsetFamily S (restrictConceptClass C S) with h𝒜_def
  -- Step 1: (restrictConceptClass C S).card = 𝒜.card (funcToSubset_injective)
  have h1 : (restrictConceptClass C S).card ≤ 𝒜.card := by
    simp only [h𝒜_def, funcToSubsetFamily]
    rw [Finset.card_image_of_injective _ (funcToSubset_injective S)]
  -- Step 2: 𝒜.card ≤ 𝒜.shatterer.card (Mathlib: card_le_card_shatterer)
  have h2 : 𝒜.card ≤ 𝒜.shatterer.card := Finset.card_le_card_shatterer 𝒜
  -- Step 3: 𝒜.shatterer.card ≤ ∑ k ∈ Iic 𝒜.vcDim, C(Fintype.card ↥S, k)
  have h3 := @Finset.card_shatterer_le_sum_vcDim ↥S _ 𝒜
  -- Step 4: vcDim(𝒜) ≤ d
  have h4 : 𝒜.vcDim ≤ d := by
    rw [← hd]; exact vcDim_restrict_le C S
  -- Step 5: Fintype.card ↥S = S.card
  have h5 : Fintype.card ↥S = S.card := Fintype.card_coe S
  -- Step 6: ∑ k ∈ Iic n, ... ≤ ∑ k ∈ range (d+1), ... when n ≤ d
  -- Iic n = range (n+1) for ℕ, and n ≤ d means range(n+1) ⊆ range(d+1)
  -- So ∑ k ∈ Iic n, C(S.card, k) ≤ ∑ k ∈ range(d+1), C(S.card, k)
  calc (restrictConceptClass C S).card
      ≤ 𝒜.card := h1
    _ ≤ 𝒜.shatterer.card := h2
    _ ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, (Fintype.card ↥S).choose k := h3
    _ = ∑ k ∈ Finset.Iic 𝒜.vcDim, S.card.choose k := by rw [h5]
    _ ≤ ∑ k ∈ Finset.Iic d, S.card.choose k := by
        apply Finset.sum_le_sum_of_subset
        exact Finset.Iic_subset_Iic.mpr h4
    _ = ∑ k ∈ Finset.range (d + 1), S.card.choose k := by
        congr 1; ext x; simp [Finset.mem_Iic, Finset.mem_range]
