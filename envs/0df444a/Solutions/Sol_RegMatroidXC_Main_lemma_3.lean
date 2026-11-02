-- Prove2me | solution 1 for RegMatroidXC.Main.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T11:30:25.300976+00:00
-- url     : https://prove2.me/submissions/4351a4b6-ce98-4cbf-8cf3-2e1e3bab89dc

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_RegMatroidXC_Main_Matroids
import Definitions.Def_RegMatroidXC_Main_Sums
open ExtensionComplexity.TSP

namespace RMXCAux

open Matrix

/-- Flexible form of an extended formulation: variables, equations and inequalities indexed by
arbitrary finite types, given by linear maps. -/
theorem isEF_of_linear {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) (r : ℕ)
    {K L J : Type*} [Fintype K] [Fintype L] [Fintype J] (hJ : Fintype.card J ≤ r)
    (A : (ι → ℝ) →ₗ[ℝ] (L → ℝ)) (B : (K → ℝ) →ₗ[ℝ] (L → ℝ)) (b : L → ℝ)
    (C : (ι → ℝ) →ₗ[ℝ] (J → ℝ)) (D : (K → ℝ) →ₗ[ℝ] (J → ℝ)) (c : J → ℝ)
    (h : ∀ x, x ∈ P ↔ ∃ y, A x + B y = b ∧ C x + D y ≤ c) : IsEFOfSize P r := by
  classical
  -- padded inequality index
  let J' := J ⊕ Fin (r - Fintype.card J)
  have hcard : Fintype.card J' = r := by
    simp only [J', Fintype.card_sum, Fintype.card_fin]; omega
  let eJ : J' ≃ Fin r := Fintype.equivFinOfCardEq hcard
  let eK : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  let eL : L ≃ Fin (Fintype.card L) := Fintype.equivFin L
  -- linear maps
  let C' : (ι → ℝ) →ₗ[ℝ] (J' → ℝ) :=
    { toFun := fun x => Sum.elim (C x) 0
      map_add' := by intro x y; ext j; cases j <;> simp
      map_smul' := by intro a x; ext j; cases j <;> simp }
  let D' : (K → ℝ) →ₗ[ℝ] (J' → ℝ) :=
    { toFun := fun y => Sum.elim (D y) 0
      map_add' := by intro x y; ext j; cases j <;> simp
      map_smul' := by intro a x; ext j; cases j <;> simp }
  let c' : J' → ℝ := Sum.elim c 0
  have hle : ∀ x y, (C' x + D' y ≤ c') ↔ (C x + D y ≤ c) := by
    intro x y
    constructor
    · intro hh j; have := hh (Sum.inl j); simpa [C', D', c'] using this
    · intro hh j; cases j with
      | inl j => simpa [C', D', c'] using hh j
      | inr j => simp [C', D', c']
  let fK : (Fin (Fintype.card K) → ℝ) →ₗ[ℝ] (K → ℝ) := LinearMap.funLeft ℝ ℝ eK
  let fL : (L → ℝ) →ₗ[ℝ] (Fin (Fintype.card L) → ℝ) := LinearMap.funLeft ℝ ℝ eL.symm
  let fJ : (J' → ℝ) →ₗ[ℝ] (Fin r → ℝ) := LinearMap.funLeft ℝ ℝ eJ.symm
  refine ⟨Fintype.card K, Fintype.card L, LinearMap.toMatrix' (fL ∘ₗ A),
    LinearMap.toMatrix' (fL ∘ₗ B ∘ₗ fK), fL b, LinearMap.toMatrix' (fJ ∘ₗ C'),
    LinearMap.toMatrix' (fJ ∘ₗ D' ∘ₗ fK), fJ c', ?_⟩
  intro x
  simp only [LinearMap.toMatrix'_mulVec, LinearMap.coe_comp, Function.comp_apply]
  rw [h]
  have keyL : ∀ u v : L → ℝ, fL u = fL v ↔ u = v := by
    intro u v; constructor
    · intro huv; funext l; have := congrFun huv (eL l); simpa [fL, LinearMap.funLeft] using this
    · intro huv; rw [huv]
  have keyJ : ∀ u v : J' → ℝ, fJ u ≤ fJ v ↔ u ≤ v := by
    intro u v; constructor
    · intro huv l; have := huv (eJ l); simpa [fJ, LinearMap.funLeft] using this
    · intro huv l; simpa [fJ, LinearMap.funLeft] using huv (eJ.symm l)
  constructor
  · rintro ⟨y, h1, h2⟩
    refine ⟨fun i => y (eK.symm i), ?_, ?_⟩
    · have hy : fK (fun i => y (eK.symm i)) = y := by
        funext k; simp [fK, LinearMap.funLeft]
      rw [hy, ← map_add, keyL]; exact h1
    · have hy : fK (fun i => y (eK.symm i)) = y := by
        funext k; simp [fK, LinearMap.funLeft]
      rw [hy, ← map_add, keyJ, hle]; exact h2
  · rintro ⟨y', h1, h2⟩
    refine ⟨fK y', ?_, ?_⟩
    · rw [← map_add, keyL] at h1; exact h1
    · rw [← map_add, keyJ, hle] at h2; exact h2

end RMXCAux

namespace RMXCAux

open Matrix RegMatroidXC.Main

theorem elim_add_elim {A B : Type*} (f g : A → ℝ) (f' g' : B → ℝ) :
    Sum.elim f f' + Sum.elim g g' = Sum.elim (f + g) (f' + g') := by
  ext j; cases j <;> rfl

theorem elim_eq_elim {A B : Type*} (f g : A → ℝ) (f' g' : B → ℝ) :
    Sum.elim f f' = Sum.elim g g' ↔ f = g ∧ f' = g' := by
  constructor
  · intro h; exact ⟨funext fun a => congrFun h (Sum.inl a), funext fun b => congrFun h (Sum.inr b)⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem elim_le_elim {A B : Type*} (f g : A → ℝ) (f' g' : B → ℝ) :
    Sum.elim f f' ≤ Sum.elim g g' ↔ f ≤ g ∧ f' ≤ g' := by
  constructor
  · intro h; exact ⟨fun a => h (Sum.inl a), fun b => h (Sum.inr b)⟩
  · rintro ⟨h1, h2⟩ j; cases j with
    | inl a => exact h1 a
    | inr b => exact h2 b

/-- Composition of extended formulations. -/
theorem isEF_compose {ι ι1 ι2 Z Q : Type*} [Fintype ι] [Fintype ι1] [Fintype ι2] [Fintype Z]
    [Fintype Q] (P : Set (ι → ℝ)) (P1 : Set (ι1 → ℝ)) (P2 : Set (ι2 → ℝ)) (r1 r2 : ℕ)
    (h1 : IsEFOfSize P1 r1) (h2 : IsEFOfSize P2 r2)
    (A : (ι → ℝ) →ₗ[ℝ] (Q → ℝ)) (B : (Z → ℝ) →ₗ[ℝ] (Q → ℝ)) (b : Q → ℝ)
    (L1 : (ι → ℝ) →ₗ[ℝ] (ι1 → ℝ)) (N1 : (Z → ℝ) →ₗ[ℝ] (ι1 → ℝ))
    (L2 : (ι → ℝ) →ₗ[ℝ] (ι2 → ℝ)) (N2 : (Z → ℝ) →ₗ[ℝ] (ι2 → ℝ))
    (hP : ∀ x, x ∈ P ↔ ∃ z, A x + B z = b ∧ L1 x + N1 z ∈ P1 ∧ L2 x + N2 z ∈ P2) :
    IsEFOfSize P (r1 + r2) := by
  obtain ⟨k1, p1, E1, F1, g1, G1, H1, c1, hE1⟩ := h1
  obtain ⟨k2, p2, E2, F2, g2, G2, H2, c2, hE2⟩ := h2
  let K := Z ⊕ (Fin k1 ⊕ Fin k2)
  let zf : (K → ℝ) →ₗ[ℝ] (Z → ℝ) := LinearMap.funLeft ℝ ℝ Sum.inl
  let y1f : (K → ℝ) →ₗ[ℝ] (Fin k1 → ℝ) := LinearMap.funLeft ℝ ℝ (fun j => Sum.inr (Sum.inl j))
  let y2f : (K → ℝ) →ₗ[ℝ] (Fin k2 → ℝ) := LinearMap.funLeft ℝ ℝ (fun j => Sum.inr (Sum.inr j))
  let A' : (ι → ℝ) →ₗ[ℝ] (Q ⊕ (Fin p1 ⊕ Fin p2) → ℝ) :=
    { toFun := fun x => Sum.elim (A x) (Sum.elim (E1 *ᵥ L1 x) (E2 *ᵥ L2 x))
      map_add' := by
        intro x y; simp only [map_add, mulVec_add, elim_add_elim]
      map_smul' := by
        intro a x; ext j; rcases j with j | j | j <;> simp [mulVec_smul] }
  let B' : (K → ℝ) →ₗ[ℝ] (Q ⊕ (Fin p1 ⊕ Fin p2) → ℝ) :=
    { toFun := fun v => Sum.elim (B (zf v))
        (Sum.elim (E1 *ᵥ N1 (zf v) + F1 *ᵥ y1f v) (E2 *ᵥ N2 (zf v) + F2 *ᵥ y2f v))
      map_add' := by
        intro x y; ext j; rcases j with j | j | j <;> simp [mulVec_add] <;> ring
      map_smul' := by
        intro a x; ext j; rcases j with j | j | j <;> simp [mulVec_smul] <;> ring }
  let C' : (ι → ℝ) →ₗ[ℝ] (Fin r1 ⊕ Fin r2 → ℝ) :=
    { toFun := fun x => Sum.elim (G1 *ᵥ L1 x) (G2 *ᵥ L2 x)
      map_add' := by
        intro x y; simp only [map_add, mulVec_add, elim_add_elim]
      map_smul' := by
        intro a x; ext j; rcases j with j | j <;> simp [mulVec_smul] }
  let D' : (K → ℝ) →ₗ[ℝ] (Fin r1 ⊕ Fin r2 → ℝ) :=
    { toFun := fun v => Sum.elim (G1 *ᵥ N1 (zf v) + H1 *ᵥ y1f v) (G2 *ᵥ N2 (zf v) + H2 *ᵥ y2f v)
      map_add' := by
        intro x y; ext j; rcases j with j | j <;> simp [mulVec_add] <;> ring
      map_smul' := by
        intro a x; ext j; rcases j with j | j <;> simp [mulVec_smul] <;> ring }
  have hcard : Fintype.card (Fin r1 ⊕ Fin r2) ≤ r1 + r2 := by simp
  refine isEF_of_linear P (r1 + r2) hcard A' B' (Sum.elim b (Sum.elim g1 g2)) C' D'
    (Sum.elim c1 c2) ?_
  intro x
  have hA : ∀ v, A' x + B' v = Sum.elim (A x + B (zf v))
      (Sum.elim (E1 *ᵥ (L1 x + N1 (zf v)) + F1 *ᵥ y1f v)
        (E2 *ᵥ (L2 x + N2 (zf v)) + F2 *ᵥ y2f v)) := by
    intro v
    simp only [A', B', LinearMap.coe_mk, AddHom.coe_mk, elim_add_elim, mulVec_add, add_assoc]
  have hC : ∀ v, C' x + D' v = Sum.elim (G1 *ᵥ (L1 x + N1 (zf v)) + H1 *ᵥ y1f v)
        (G2 *ᵥ (L2 x + N2 (zf v)) + H2 *ᵥ y2f v) := by
    intro v
    simp only [C', D', LinearMap.coe_mk, AddHom.coe_mk, elim_add_elim, mulVec_add, add_assoc]
  simp_rw [hA, hC, elim_eq_elim, elim_le_elim]
  rw [hP]
  constructor
  · rintro ⟨z, hz, hz1, hz2⟩
    obtain ⟨y1, hy1, hy1'⟩ := (hE1 _).1 hz1
    obtain ⟨y2, hy2, hy2'⟩ := (hE2 _).1 hz2
    exact ⟨Sum.elim z (Sum.elim y1 y2), ⟨hz, hy1, hy2⟩, hy1', hy2'⟩
  · rintro ⟨v, ⟨hz, hy1, hy2⟩, hy1', hy2'⟩
    exact ⟨zf v, hz, (hE1 _).2 ⟨_, hy1, hy1'⟩, (hE2 _).2 ⟨_, hy2, hy2'⟩⟩

/-! ### Matroid facts via cycles -/

section Matroids

variable {α : Type}

theorem isCycle_empty (N : Matroid α) : IsCycle N ∅ :=
  ⟨Set.empty_subset _, ∅, by simp, by simp, by simp⟩

theorem isCycle_of_isCircuit (N : Matroid α) {C : Set α} (hC : N.IsCircuit C) : IsCycle N C :=
  ⟨hC.subset_ground, {C}, by simp, by simpa using hC, by simp⟩

theorem indep_iff_cycles (N : Matroid α) (I : Set α) :
    N.Indep I ↔ I ⊆ N.E ∧ ∀ C, IsCycle N C → C ⊆ I → C = ∅ := by
  constructor
  · intro hI
    refine ⟨hI.subset_ground, ?_⟩
    rintro C ⟨-, S, -, hS, rfl⟩ hCI
    rw [Set.sUnion_eq_empty]
    intro D hD
    by_contra hne
    exact (hS D hD).not_indep (hI.subset (fun x hx => hCI ⟨D, hD, hx⟩))
  · rintro ⟨hIE, h⟩
    by_contra hI
    have hdep : N.Dep I := ⟨hI, hIE⟩
    obtain ⟨C, hCI, hC⟩ := hdep.exists_isCircuit_subset
    have := h C (isCycle_of_isCircuit N hC) hCI
    exact hC.nonempty.ne_empty this

theorem cycleSum_symm {M M₁ M₂ : Matroid α} (h : IsCycleSum M M₁ M₂) : IsCycleSum M M₂ M₁ := by
  refine ⟨by rw [h.1, symmDiff_comm], fun C => ?_⟩
  rw [h.2 C]
  constructor
  · rintro ⟨C₁, C₂, h1, h2, h3, h4⟩; exact ⟨C₂, C₁, h2, h1, by rw [h3, symmDiff_comm], h4⟩
  · rintro ⟨C₁, C₂, h1, h2, h3, h4⟩; exact ⟨C₂, C₁, h2, h1, by rw [h3, symmDiff_comm], h4⟩

theorem factA {M M₁ M₂ : Matroid α} (h : IsCycleSum M M₁ M₂) {I : Set α} (hI : M.Indep I) :
    M₁.Indep (I ∩ M₁.E) := by
  rw [indep_iff_cycles]
  refine ⟨Set.inter_subset_right, fun C hC hCI => ?_⟩
  have hCM : IsCycle M C := by
    rw [h.2 C]
    exact ⟨C, ∅, hC, isCycle_empty _, by ext; simp [Set.mem_symmDiff],
      (Set.Subset.trans hCI Set.inter_subset_left).trans hI.subset_ground⟩
  exact ((indep_iff_cycles M I).1 hI).2 C hCM (hCI.trans Set.inter_subset_left)

theorem factB1 {M M₁ M₂ : Matroid α} (h : IsCycleSum M M₁ M₂) (hd : Disjoint M₁.E M₂.E)
    {J₁ J₂ : Set α} (h1 : M₁.Indep J₁) (h2 : M₂.Indep J₂) : M.Indep (J₁ ∪ J₂) := by
  have hE1 := h1.subset_ground
  have hE2 := h2.subset_ground
  rw [indep_iff_cycles]
  refine ⟨?_, ?_⟩
  · rw [h.1]
    rintro e (he | he)
    · exact Or.inl ⟨hE1 he, fun h' => Set.disjoint_left.1 hd (hE1 he) h'⟩
    · exact Or.inr ⟨hE2 he, fun h' => Set.disjoint_left.1 hd h' (hE2 he)⟩
  · intro C hC hCZ
    obtain ⟨C₁, C₂, hC₁, hC₂, rfl, -⟩ := (h.2 C).1 hC
    have hC1E := hC₁.1
    have hC2E := hC₂.1
    have k1 : C₁ ⊆ J₁ := by
      intro e he
      have heE : e ∈ M₁.E := hC1E he
      have he2 : e ∉ C₂ := fun h' => Set.disjoint_left.1 hd heE (hC2E h')
      have := hCZ (Or.inl ⟨he, he2⟩)
      rcases this with h' | h'
      · exact h'
      · exact absurd (hE2 h') (Set.disjoint_left.1 hd heE)
    have k2 : C₂ ⊆ J₂ := by
      intro e he
      have heE : e ∈ M₂.E := hC2E he
      have he1 : e ∉ C₁ := fun h' => Set.disjoint_left.1 hd (hC1E h') heE
      have := hCZ (Or.inr ⟨he, he1⟩)
      rcases this with h' | h'
      · exact absurd heE (Set.disjoint_left.1 hd (hE1 h'))
      · exact h'
    rw [((indep_iff_cycles _ _).1 h1).2 C₁ hC₁ k1, ((indep_iff_cycles _ _).1 h2).2 C₂ hC₂ k2]
    simp

theorem factB2 {M M₁ M₂ : Matroid α} (h : IsCycleSum M M₁ M₂) {a : α}
    (ha : M₁.E ∩ M₂.E = {a})
    {J₁ J₂ : Set α} (h1 : M₁.Indep J₁) (h2 : M₂.Indep J₂) (haJ1 : a ∈ J₁) (haJ2 : a ∉ J₂) :
    M.Indep ((J₁ \ {a}) ∪ J₂) := by
  have hE1 := h1.subset_ground
  have hE2 := h2.subset_ground
  have key : ∀ e, e ∈ M₁.E → e ∈ M₂.E → e = a := by
    intro e h1 h2
    have : e ∈ M₁.E ∩ M₂.E := ⟨h1, h2⟩
    rw [ha] at this; exact this
  rw [indep_iff_cycles]
  refine ⟨?_, ?_⟩
  · rw [h.1]
    rintro e (⟨he, hne⟩ | he)
    · exact Or.inl ⟨hE1 he, fun h' => hne (key e (hE1 he) h')⟩
    · exact Or.inr ⟨hE2 he, fun h' => haJ2 (key e h' (hE2 he) ▸ he)⟩
  · intro C hC hCZ
    obtain ⟨C₁, C₂, hC₁, hC₂, rfl, -⟩ := (h.2 C).1 hC
    have hC1E := hC₁.1
    have hC2E := hC₂.1
    have k1 : C₁ ⊆ J₁ := by
      intro e he
      by_cases hea : e = a
      · rw [hea]; exact haJ1
      have he2 : e ∉ C₂ := fun h' => hea (key e (hC1E he) (hC2E h'))
      rcases hCZ (Or.inl ⟨he, he2⟩) with h' | h'
      · exact h'.1
      · exact absurd (key e (hC1E he) (hE2 h')) hea
    have hC1 : C₁ = ∅ := ((indep_iff_cycles _ _).1 h1).2 C₁ hC₁ k1
    subst hC1
    have k2 : C₂ ⊆ J₂ := by
      intro e he
      rcases hCZ (Or.inr ⟨he, by simp⟩) with h' | h'
      · exact absurd (key e (hE1 h'.1) (hC2E he)) h'.2
      · exact h'
    rw [((indep_iff_cycles _ _).1 h2).2 C₂ hC₂ k2]
    simp

theorem factC {M M₁ M₂ : Matroid α} (h : IsCycleSum M M₁ M₂) {a : α}
    (ha : M₁.E ∩ M₂.E = {a}) (hloop : ¬ M₁.IsLoop a) {I : Set α} (hI : M.Indep I) :
    M₁.Indep (insert a (I ∩ M₁.E)) ∨ M₂.Indep (insert a (I ∩ M₂.E)) := by
  have haE : a ∈ M₁.E ∩ M₂.E := by rw [ha]; rfl
  by_contra hcon
  push Not at hcon
  obtain ⟨n1, n2⟩ := hcon
  have i1 := factA h hI
  have i2 := factA (cycleSum_symm h) hI
  have hD : ∀ (N : Matroid α), a ∈ N.E → N.Indep (I ∩ N.E) → ¬ N.Indep (insert a (I ∩ N.E)) →
      ∃ D, N.IsCircuit D ∧ a ∈ D ∧ D ⊆ insert a (I ∩ N.E) := by
    intro N haN hi hn
    have hdep : N.Dep (insert a (I ∩ N.E)) :=
      ⟨hn, Set.insert_subset haN Set.inter_subset_right⟩
    obtain ⟨D, hDs, hD⟩ := hdep.exists_isCircuit_subset
    refine ⟨D, hD, ?_, hDs⟩
    by_contra haD
    apply hD.not_indep
    apply hi.subset
    intro e he
    rcases hDs he with rfl | h'
    · exact absurd he haD
    · exact h'
  obtain ⟨D₁, hD₁, haD₁, hD₁s⟩ := hD M₁ haE.1 i1 n1
  obtain ⟨D₂, hD₂, haD₂, hD₂s⟩ := hD M₂ haE.2 i2 n2
  have hsub : symmDiff D₁ D₂ ⊆ I := by
    rintro e (⟨he1, he2⟩ | ⟨he2, he1⟩)
    · rcases hD₁s he1 with rfl | h'
      · exact absurd haD₂ he2
      · exact h'.1
    · rcases hD₂s he2 with rfl | h'
      · exact absurd haD₁ he1
      · exact h'.1
  have hcyc : IsCycle M (symmDiff D₁ D₂) := by
    rw [h.2]
    exact ⟨D₁, D₂, isCycle_of_isCircuit _ hD₁, isCycle_of_isCircuit _ hD₂, rfl,
      hsub.trans hI.subset_ground⟩
  have h0 := ((indep_iff_cycles M I).1 hI).2 _ hcyc hsub
  have heq : D₁ = D₂ := by
    rw [Set.ext_iff] at h0
    ext e
    have := h0 e
    simp only [Set.mem_symmDiff, Set.mem_empty_iff_false, iff_false, not_or, not_and,
      not_not] at this
    exact ⟨fun h1 => this.1 h1, fun h2 => this.2 h2⟩
  have hsing : D₁ = {a} := by
    ext e
    constructor
    · intro he
      have : e ∈ M₁.E ∩ M₂.E := ⟨hD₁.subset_ground he, hD₂.subset_ground (heq ▸ he)⟩
      rw [ha] at this; exact this
    · rintro rfl; exact haD₁
  rw [hsing] at hD₁
  exact hloop (Matroid.singleton_isCircuit.1 hD₁)

end Matroids

/-! ### Polytopes -/

section Poly

variable {α : Type}

/-- characteristic vector -/
noncomputable def chi (N : Matroid α) (I : Set α) : N.E → ℝ :=
  fun e => I.indicator (fun _ => (1 : ℝ)) (e : α)

theorem mem_indepPolytope_iff (N : Matroid α) (x : N.E → ℝ) :
    x ∈ indepPolytope N ↔ ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (J : ι → Set α),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i, N.Indep (J i)) ∧ x = ∑ i, w i • chi N (J i) := by
  unfold indepPolytope
  constructor
  · intro hx
    rw [mem_convexHull_iff_exists_fintype] at hx
    obtain ⟨ι, _, w, z, hw0, hw1, hz, hx⟩ := hx
    choose J hJ hzJ using hz
    refine ⟨ι, inferInstance, w, J, hw0, hw1, hJ, ?_⟩
    rw [← hx]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    funext e
    exact hzJ i e
  · rintro ⟨ι, _, w, J, hw0, hw1, hJ, rfl⟩
    exact mem_convexHull_of_exists_fintype w (fun i => chi N (J i)) hw0 hw1
      (fun i => ⟨J i, hJ i, fun e => rfl⟩) rfl

theorem chi_mem (N : Matroid α) {I : Set α} (hI : N.Indep I) : chi N I ∈ indepPolytope N :=
  subset_convexHull ℝ _ ⟨I, hI, fun e => rfl⟩

open Classical in
/-- extension of a vector on `M.E` to `N.E`, with value `t` outside `M.E`. -/
noncomputable def ext (M N : Matroid α) (x : M.E → ℝ) (t : ℝ) : N.E → ℝ :=
  fun e => if h : (e : α) ∈ M.E then x ⟨e, h⟩ else t

open Classical in
theorem ext_chi (M N : Matroid α) (I : Set α) (t : ℝ) :
    ext M N (chi M I) t = fun e : N.E => if (e : α) ∈ M.E then I.indicator (fun _ => (1:ℝ)) (e : α)
      else t := by
  funext e; simp only [ext, chi]; split_ifs <;> rfl

theorem ext_comb (M N : Matroid α) (x x' : M.E → ℝ) (t t' a b : ℝ) :
    ext M N (a • x + b • x') (a * t + b * t') = a • ext M N x t + b • ext M N x' t' := by
  funext e; simp only [ext, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; split_ifs <;> rfl

/-- 1-sum polytope. -/
theorem poly_oneSum {M M₁ M₂ : Matroid α} (h : IsCycleSum M M₁ M₂) (hd : Disjoint M₁.E M₂.E)
    [Fintype M.E] [Fintype M₁.E] [Fintype M₂.E] (x : M.E → ℝ) :
    x ∈ indepPolytope M ↔ ext M M₁ x 0 ∈ indepPolytope M₁ ∧ ext M M₂ x 0 ∈ indepPolytope M₂ := by
  classical
  constructor
  · intro hx
    let R : Set (M.E → ℝ) :=
      {x | ext M M₁ x 0 ∈ indepPolytope M₁ ∧ ext M M₂ x 0 ∈ indepPolytope M₂}
    have hR : Convex ℝ R := by
      rintro x1 ⟨h11, h12⟩ x2 ⟨h21, h22⟩ a b ha hb hab
      have e1 := ext_comb M M₁ x1 x2 0 0 a b
      have e2 := ext_comb M M₂ x1 x2 0 0 a b
      simp only [mul_zero, add_zero] at e1 e2
      refine ⟨?_, ?_⟩
      · rw [e1]; exact (convex_convexHull ℝ _) h11 h21 ha hb hab
      · rw [e2]; exact (convex_convexHull ℝ _) h12 h22 ha hb hab
    have hsub : {x : M.E → ℝ | ∃ I : Set α, M.Indep I ∧
        ∀ e : M.E, x e = I.indicator (fun _ => (1 : ℝ)) (e : α)} ⊆ R := by
      rintro x ⟨I, hI, hxI⟩
      have hx : x = chi M I := funext hxI
      subst hx
      refine ⟨?_, ?_⟩
      · have : ext M M₁ (chi M I) 0 = chi M₁ (I ∩ M₁.E) := by
          rw [ext_chi]; funext e
          have heM : (e : α) ∈ M.E := by
            rw [h.1]; exact Or.inl ⟨e.2, fun h' => Set.disjoint_left.1 hd e.2 h'⟩
          simp [heM, chi, Set.indicator, e.2]
        rw [this]; exact chi_mem _ (factA h hI)
      · have : ext M M₂ (chi M I) 0 = chi M₂ (I ∩ M₂.E) := by
          rw [ext_chi]; funext e
          have heM : (e : α) ∈ M.E := by
            rw [h.1]; exact Or.inr ⟨e.2, fun h' => Set.disjoint_left.1 hd h' e.2⟩
          simp [heM, chi, Set.indicator, e.2]
        rw [this]; exact chi_mem _ (factA (cycleSum_symm h) hI)
    exact convexHull_min hsub hR hx
  · rintro ⟨h1, h2⟩
    obtain ⟨ι1, _, w1, J1, hw10, hw11, hJ1, hx1⟩ := (mem_indepPolytope_iff _ _).1 h1
    obtain ⟨ι2, _, w2, J2, hw20, hw21, hJ2, hx2⟩ := (mem_indepPolytope_iff _ _).1 h2
    rw [mem_indepPolytope_iff]
    refine ⟨ι1 × ι2, inferInstance, fun ij => w1 ij.1 * w2 ij.2, fun ij => J1 ij.1 ∪ J2 ij.2,
      fun ij => mul_nonneg (hw10 _) (hw20 _), ?_, fun ij => factB1 h hd (hJ1 _) (hJ2 _), ?_⟩
    · rw [Fintype.sum_prod_type]; simp [← Finset.mul_sum, hw21, hw11]
    · funext e
      have hE : (e : α) ∈ M₁.E ∨ (e : α) ∈ M₂.E := by
        have hmem : (e : α) ∈ symmDiff M₁.E M₂.E := by rw [← h.1]; exact e.2
        rcases hmem with h' | h'
        · exact Or.inl h'.1
        · exact Or.inr h'.1
      rw [Finset.sum_apply, Fintype.sum_prod_type]
      rcases hE with he | he
      · have hx := congrFun hx1 ⟨e, he⟩
        simp only [ext, e.2, dif_pos, Subtype.coe_eta, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul] at hx
        rw [hx]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have hnot : ∀ j, (e : α) ∉ J2 j := fun j h' =>
          Set.disjoint_left.1 hd he ((hJ2 j).subset_ground h')
        simp only [Pi.smul_apply, smul_eq_mul, chi, Set.indicator, Set.mem_union, hnot, or_false]
        rw [← Finset.sum_mul, ← Finset.mul_sum, hw21, mul_one]
      · have hx := congrFun hx2 ⟨e, he⟩
        simp only [ext, e.2, dif_pos, Subtype.coe_eta, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul] at hx
        rw [hx]
        have hnot : ∀ i, (e : α) ∉ J1 i := fun i h' =>
          Set.disjoint_left.1 hd ((hJ1 i).subset_ground h') he
        simp only [Pi.smul_apply, smul_eq_mul, chi, Set.indicator, Set.mem_union, hnot, false_or]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← Finset.sum_mul, ← Finset.sum_mul, hw11, one_mul]

end Poly

end RMXCAux

namespace RMXCAux

open Matrix RegMatroidXC.Main

/-! ### Coupling of two convex combinations -/

section Coupling

variable {ι1 ι2 : Type} [Fintype ι1] [Fintype ι2]

open Classical in
/-- the coupling weights -/
noncomputable def cpl (l : ι1 → ℝ) (m : ι2 → ℝ) (p : ι1 → Prop) (q : ι2 → Prop) (y y' : ℝ)
    (ij : ι1 × ι2) : ℝ :=
  if p ij.1 then (if q ij.2 then 0 else l ij.1 * m ij.2 / y)
  else (if q ij.2 then l ij.1 * m ij.2 / y' else 0)

open Classical in
theorem coupling (l : ι1 → ℝ) (m : ι2 → ℝ) (p : ι1 → Prop) (q : ι2 → Prop)
    (hl0 : ∀ i, 0 ≤ l i) (hl1 : ∑ i, l i = 1) (hm0 : ∀ j, 0 ≤ m j) (hm1 : ∑ j, m j = 1)
    (y y' : ℝ) (hy : y = ∑ i, if p i then l i else 0) (hy' : y' = ∑ j, if q j then m j else 0)
    (hyy : y + y' = 1) :
    (∀ ij, 0 ≤ cpl l m p q y y' ij) ∧
    (∀ f : ι1 → ℝ, ∑ ij, cpl l m p q y y' ij * f ij.1 = ∑ i, l i * f i) ∧
    (∀ g : ι2 → ℝ, ∑ ij, cpl l m p q y y' ij * g ij.2 = ∑ j, m j * g j) ∧
    (∀ ij, cpl l m p q y y' ij ≠ 0 → (p ij.1 ∧ ¬ q ij.2) ∨ (¬ p ij.1 ∧ q ij.2)) := by
  have hy0 : 0 ≤ y := by
    rw [hy]; exact Finset.sum_nonneg (fun i _ => by split_ifs; exacts [hl0 i, le_rfl])
  have hy'0 : 0 ≤ y' := by
    rw [hy']; exact Finset.sum_nonneg (fun j _ => by split_ifs; exacts [hm0 j, le_rfl])
  -- complementary sums
  have hcy : (∑ i, if p i then 0 else l i) = y' := by
    have : ∀ i, (if p i then 0 else l i) = l i - (if p i then l i else 0) := by
      intro i; split_ifs <;> ring
    simp_rw [this]; rw [Finset.sum_sub_distrib, hl1, ← hy]; linarith
  have hcy' : (∑ j, if q j then 0 else m j) = y := by
    have : ∀ j, (if q j then 0 else m j) = m j - (if q j then m j else 0) := by
      intro j; split_ifs <;> ring
    simp_rw [this]; rw [Finset.sum_sub_distrib, hm1, ← hy']; linarith
  have lle : ∀ i, p i → l i ≤ y := by
    intro i hi
    have := Finset.single_le_sum (f := fun k => if p k then l k else 0)
      (fun k _ => by split_ifs; exacts [hl0 k, le_rfl]) (Finset.mem_univ i)
    simpa [hi, ← hy] using this
  have lle' : ∀ i, ¬ p i → l i ≤ y' := by
    intro i hi
    have := Finset.single_le_sum (f := fun k => if p k then 0 else l k)
      (fun k _ => by split_ifs; exacts [le_rfl, hl0 k]) (Finset.mem_univ i)
    simpa [hi, hcy] using this
  have mle : ∀ j, q j → m j ≤ y' := by
    intro j hj
    have := Finset.single_le_sum (f := fun k => if q k then m k else 0)
      (fun k _ => by split_ifs; exacts [hm0 k, le_rfl]) (Finset.mem_univ j)
    simpa [hj, ← hy'] using this
  have mle' : ∀ j, ¬ q j → m j ≤ y := by
    intro j hj
    have := Finset.single_le_sum (f := fun k => if q k then 0 else m k)
      (fun k _ => by split_ifs; exacts [le_rfl, hm0 k]) (Finset.mem_univ j)
    simpa [hj, hcy'] using this
  -- `t / s * s = t` when `t ≤ s`, `0 ≤ t`
  have hdiv : ∀ t s : ℝ, 0 ≤ t → t ≤ s → t / s * s = t := by
    intro t s ht hts
    rcases eq_or_lt_of_le (ht.trans hts) with hs | hs
    · rw [← hs] at hts ⊢; have : t = 0 := le_antisymm hts ht
      rw [this]; simp
    · field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ij; unfold cpl
    split_ifs
    · exact le_rfl
    · exact div_nonneg (mul_nonneg (hl0 _) (hm0 _)) hy0
    · exact div_nonneg (mul_nonneg (hl0 _) (hm0 _)) hy'0
    · exact le_rfl
  · intro f
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [cpl]
    by_cases hi : p i
    · simp only [hi, if_true]
      have : ∀ j, (if q j then (0:ℝ) else l i * m j / y) * f i =
          l i / y * f i * (if q j then 0 else m j) := by
        intro j; split_ifs <;> ring
      simp_rw [this]
      rw [← Finset.mul_sum, hcy']
      have := hdiv (l i) y (hl0 i) (lle i hi)
      calc l i / y * f i * y = (l i / y * y) * f i := by ring
        _ = l i * f i := by rw [this]
    · simp only [hi, if_false]
      have : ∀ j, (if q j then l i * m j / y' else 0) * f i =
          l i / y' * f i * (if q j then m j else 0) := by
        intro j; split_ifs <;> ring
      simp_rw [this]
      rw [← Finset.mul_sum, ← hy']
      have := hdiv (l i) y' (hl0 i) (lle' i hi)
      calc l i / y' * f i * y' = (l i / y' * y') * f i := by ring
        _ = l i * f i := by rw [this]
  · intro g
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [cpl]
    by_cases hj : q j
    · simp only [hj, if_true]
      have : ∀ i, (if p i then (0:ℝ) else l i * m j / y') * g j =
          m j / y' * g j * (if p i then 0 else l i) := by
        intro i; split_ifs <;> ring
      simp_rw [this]
      rw [← Finset.mul_sum, hcy]
      have := hdiv (m j) y' (hm0 j) (mle j hj)
      calc m j / y' * g j * y' = (m j / y' * y') * g j := by ring
        _ = m j * g j := by rw [this]
    · simp only [hj, if_false]
      have : ∀ i, (if p i then l i * m j / y else 0) * g j =
          m j / y * g j * (if p i then l i else 0) := by
        intro i; split_ifs <;> ring
      simp_rw [this]
      rw [← Finset.mul_sum, ← hy]
      have := hdiv (m j) y (hm0 j) (mle' j hj)
      calc m j / y * g j * y = (m j / y * y) * g j := by ring
        _ = m j * g j := by rw [this]
  · intro ij hne
    unfold cpl at hne
    by_cases h1 : p ij.1 <;> by_cases h2 : q ij.2 <;> simp_all

end Coupling

section TwoSum

variable {α : Type}

theorem poly_twoSum {M M₁ M₂ : Matroid α} (h : IsCycleSum M M₁ M₂) {a : α}
    (ha : M₁.E ∩ M₂.E = {a}) (hl1 : ¬ M₁.IsLoop a) (hl2 : ¬ M₂.IsLoop a)
    [Fintype M.E] [Fintype M₁.E] [Fintype M₂.E] (x : M.E → ℝ) :
    x ∈ indepPolytope M ↔ ∃ y y' : ℝ, y + y' = 1 ∧ ext M M₁ x y ∈ indepPolytope M₁ ∧
      ext M M₂ x y' ∈ indepPolytope M₂ := by
  classical
  have haE : a ∈ M₁.E ∩ M₂.E := by rw [ha]; rfl
  have key : ∀ e, e ∈ M₁.E → e ∈ M₂.E → e = a := by
    intro e h1 h2
    have : e ∈ M₁.E ∩ M₂.E := ⟨h1, h2⟩
    rw [ha] at this; exact this
  have hM1 : ∀ e ∈ M₁.E, (e ∈ M.E ↔ e ≠ a) := by
    intro e he
    rw [h.1, Set.mem_symmDiff]
    constructor
    · rintro (⟨-, h2⟩ | ⟨h2, h1⟩)
      · rintro rfl; exact h2 haE.2
      · exact absurd he h1
    · intro hne; exact Or.inl ⟨he, fun h2 => hne (key e he h2)⟩
  have hM2 : ∀ e ∈ M₂.E, (e ∈ M.E ↔ e ≠ a) := by
    intro e he
    rw [h.1, Set.mem_symmDiff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨-, h1⟩)
      · exact absurd he h2
      · rintro rfl; exact h1 haE.1
    · intro hne; exact Or.inr ⟨he, fun h1 => hne (key e h1 he)⟩
  have haM : a ∉ M.E := fun h' => (hM1 a haE.1).1 h' rfl
  constructor
  · intro hx
    let R : Set (M.E → ℝ) := {x | ∃ y y' : ℝ, y + y' = 1 ∧ ext M M₁ x y ∈ indepPolytope M₁ ∧
      ext M M₂ x y' ∈ indepPolytope M₂}
    have hR : Convex ℝ R := by
      rintro x1 ⟨y1, y1', hs1, h11, h12⟩ x2 ⟨y2, y2', hs2, h21, h22⟩ s t hs ht hst
      refine ⟨s * y1 + t * y2, s * y1' + t * y2', ?_, ?_, ?_⟩
      · calc s * y1 + t * y2 + (s * y1' + t * y2') = s * (y1 + y1') + t * (y2 + y2') := by ring
          _ = 1 := by rw [hs1, hs2, mul_one, mul_one, hst]
      · rw [ext_comb]; exact (convex_convexHull ℝ _) h11 h21 hs ht hst
      · rw [ext_comb]; exact (convex_convexHull ℝ _) h12 h22 hs ht hst
    have hsub : {x : M.E → ℝ | ∃ I : Set α, M.Indep I ∧
        ∀ e : M.E, x e = I.indicator (fun _ => (1 : ℝ)) (e : α)} ⊆ R := by
      rintro x ⟨I, hI, hxI⟩
      have hx : x = chi M I := funext hxI
      subst hx
      have hIa : a ∉ I := fun h' => haM (hI.subset_ground h')
      have e1 : ∀ t : ℝ, (t = 0 ∨ t = 1) → ext M M₁ (chi M I) t =
          chi M₁ (if t = 1 then insert a (I ∩ M₁.E) else I ∩ M₁.E) := by
        intro t ht01; rw [ext_chi]; funext e
        by_cases hea : (e : α) = a
        · have : (e : α) ∉ M.E := by rw [hM1 _ e.2]; simpa using hea
          by_cases ht : t = 1
          · simp [this, ht, chi, hea, haM]
          · have ht0 : t = 0 := by tauto
            simp [this, ht, ht0, chi, hea, Set.indicator, hIa, haM]
        · have : (e : α) ∈ M.E := (hM1 _ e.2).2 hea
          by_cases ht : t = 1 <;> simp [this, ht, chi, hea, Set.indicator, e.2]
      have e2 : ∀ t : ℝ, (t = 0 ∨ t = 1) → ext M M₂ (chi M I) t =
          chi M₂ (if t = 1 then insert a (I ∩ M₂.E) else I ∩ M₂.E) := by
        intro t ht01; rw [ext_chi]; funext e
        by_cases hea : (e : α) = a
        · have : (e : α) ∉ M.E := by rw [hM2 _ e.2]; simpa using hea
          by_cases ht : t = 1
          · simp [this, ht, chi, hea, haM]
          · have ht0 : t = 0 := by tauto
            simp [this, ht, ht0, chi, hea, Set.indicator, hIa, haM]
        · have : (e : α) ∈ M.E := (hM2 _ e.2).2 hea
          by_cases ht : t = 1 <;> simp [this, ht, chi, hea, Set.indicator, e.2]
      rcases factC h ha hl1 hI with hc | hc
      · refine ⟨1, 0, by norm_num, ?_, ?_⟩
        · rw [e1 1 (by norm_num)]; simpa using chi_mem _ hc
        · rw [e2 0 (by norm_num)]; simpa using chi_mem _ (factA (cycleSum_symm h) hI)
      · refine ⟨0, 1, by norm_num, ?_, ?_⟩
        · rw [e1 0 (by norm_num)]; simpa using chi_mem _ (factA h hI)
        · rw [e2 1 (by norm_num)]; simpa using chi_mem _ hc
    exact convexHull_min hsub hR hx
  · rintro ⟨y, y', hyy, h1, h2⟩
    obtain ⟨ι1, _, l, J, hl0, hl1', hJ, hx1⟩ := (mem_indepPolytope_iff _ _).1 h1
    obtain ⟨ι2, _, m, K, hm0, hm1, hK, hx2⟩ := (mem_indepPolytope_iff _ _).1 h2
    have hy : y = ∑ i, if a ∈ J i then l i else 0 := by
      have := congrFun hx1 ⟨a, haE.1⟩
      simp only [ext, haM, dif_neg, not_false_eq_true, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, chi, Set.indicator] at this
      rw [this]; refine Finset.sum_congr rfl (fun i _ => ?_); split_ifs <;> simp
    have hy' : y' = ∑ j, if a ∈ K j then m j else 0 := by
      have := congrFun hx2 ⟨a, haE.2⟩
      simp only [ext, haM, dif_neg, not_false_eq_true, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, chi, Set.indicator] at this
      rw [this]; refine Finset.sum_congr rfl (fun j _ => ?_); split_ifs <;> simp
    obtain ⟨hν0, hνf, hνg, hνne⟩ := coupling l m (fun i => a ∈ J i) (fun j => a ∈ K j)
      hl0 hl1' hm0 hm1 y y' hy hy' hyy
    set ν := cpl l m (fun i => a ∈ J i) (fun j => a ∈ K j) y y' with hν
    let good : ι1 × ι2 → Prop := fun ij =>
      (a ∈ J ij.1 ∧ a ∉ K ij.2) ∨ (a ∉ J ij.1 ∧ a ∈ K ij.2)
    let Z : ι1 × ι2 → Set α := fun ij => if good ij then (J ij.1 ∪ K ij.2) \ {a} else ∅
    have hZ : ∀ ij, M.Indep (Z ij) := by
      intro ij
      simp only [Z]
      split_ifs with hg
      · rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have := factB2 h ha (hJ ij.1) (hK ij.2) h1 h2
          convert this using 1
          ext e; simp only [Set.mem_diff, Set.mem_union, Set.mem_singleton_iff]
          constructor
          · rintro ⟨h | h, hne⟩
            · exact Or.inl ⟨h, hne⟩
            · exact Or.inr h
          · rintro (⟨h, hne⟩ | h)
            · exact ⟨Or.inl h, hne⟩
            · exact ⟨Or.inr h, fun h' => h2 (h' ▸ h)⟩
        · have ha' : M₂.E ∩ M₁.E = {a} := by rw [Set.inter_comm]; exact ha
          have := factB2 (cycleSum_symm h) ha' (hK ij.2) (hJ ij.1) h2 h1
          convert this using 1
          ext e; simp only [Set.mem_diff, Set.mem_union, Set.mem_singleton_iff]
          constructor
          · rintro ⟨h | h, hne⟩
            · exact Or.inr h
            · exact Or.inl ⟨h, hne⟩
          · rintro (⟨h, hne⟩ | h)
            · exact ⟨Or.inr h, hne⟩
            · exact ⟨Or.inl h, fun h' => h1 (h' ▸ h)⟩
      · exact Matroid.empty_indep M
    rw [mem_indepPolytope_iff]
    refine ⟨ι1 × ι2, inferInstance, ν, Z, hν0, ?_, hZ, ?_⟩
    · have := hνf (fun _ => 1); simpa [hl1'] using this
    · funext e
      rw [Finset.sum_apply]
      have hmem : (e : α) ∈ symmDiff M₁.E M₂.E := by rw [← h.1]; exact e.2
      have hea : (e : α) ≠ a := fun h' => haM (h' ▸ e.2)
      -- each term
      have hterm : ∀ ij, (ν ij • chi M (Z ij)) e =
          ν ij * (if (e : α) ∈ J ij.1 ∪ K ij.2 then 1 else 0) := by
        intro ij
        simp only [Pi.smul_apply, smul_eq_mul, chi, Z, Set.indicator]
        by_cases hg : good ij
        · simp [hg, hea]
        · have : ν ij = 0 := by
            by_contra hne; exact hg (hνne ij hne)
          simp [this]
      simp_rw [hterm]
      rcases hmem with ⟨he1, he2⟩ | ⟨he2, he1⟩
      · have hnK : ∀ j, (e : α) ∉ K j := fun j h' => he2 ((hK j).subset_ground h')
        have := congrFun hx1 ⟨e, he1⟩
        simp only [ext, e.2, dif_pos, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, chi,
          Set.indicator] at this
        rw [this]
        simp only [Set.mem_union, hnK, or_false]
        exact (hνf (fun i => if (e : α) ∈ J i then 1 else 0)).symm
      · have hnJ : ∀ i, (e : α) ∉ J i := fun i h' => he1 ((hJ i).subset_ground h')
        have := congrFun hx2 ⟨e, he2⟩
        simp only [ext, e.2, dif_pos, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, chi,
          Set.indicator] at this
        rw [this]
        simp only [Set.mem_union, hnJ, false_or]
        exact (hνg (fun j => if (e : α) ∈ K j then 1 else 0)).symm

end TwoSum

section Final

variable {α : Type}

open Classical in
/-- the linear extension map -/
noncomputable def extLin (M N : Matroid α) : (M.E → ℝ) →ₗ[ℝ] (N.E → ℝ) :=
  { toFun := fun x => ext M N x 0
    map_add' := by
      intro x y; funext e; simp only [ext, Pi.add_apply]; split_ifs <;> simp
    map_smul' := by
      intro c x; funext e; simp only [ext, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      split_ifs <;> simp }

open Classical in
/-- the extra coordinate -/
noncomputable def extraLin (M N : Matroid α) (k : Fin 2) : (Fin 2 → ℝ) →ₗ[ℝ] (N.E → ℝ) :=
  { toFun := fun z e => if (e : α) ∈ M.E then 0 else z k
    map_add' := by
      intro x y; funext e; simp only [Pi.add_apply]; split_ifs <;> simp
    map_smul' := by
      intro c x; funext e; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      split_ifs <;> simp }

theorem extLin_add (M N : Matroid α) (x : M.E → ℝ) (z : Fin 2 → ℝ) (k : Fin 2) :
    extLin M N x + extraLin M N k z = ext M N x (z k) := by
  classical
  funext e; simp only [extLin, extraLin, ext, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]
  split_ifs <;> simp

theorem lemma3_aux (M M₁ M₂ : Matroid α) [Fintype M.E] [Fintype M₁.E] [Fintype M₂.E]
    (hsum : IsOneSum M M₁ M₂ ∨ IsTwoSum M M₁ M₂) (r₁ r₂ : ℕ)
    (h₁ : IsEFOfSize (indepPolytope M₁) r₁) (h₂ : IsEFOfSize (indepPolytope M₂) r₂) :
    ∃ r : ℕ, IsEFOfSize (indepPolytope M) r ∧ r ≤ r₁ + r₂ := by
  refine ⟨r₁ + r₂, ?_, le_rfl⟩
  rcases hsum with ⟨-, -, hcs, hd, -, -⟩ | ⟨-, -, hcs, a, ha, hl1, -, hl2, -, -, -⟩
  · refine isEF_compose (Z := Fin 0) (Q := Fin 0) _ _ _ r₁ r₂ h₁ h₂ 0 0 0
      (extLin M M₁) 0 (extLin M M₂) 0 ?_
    intro x
    rw [poly_oneSum hcs hd]
    constructor
    · rintro ⟨k1, k2⟩
      exact ⟨0, by simp, by simpa [extLin] using k1, by simpa [extLin] using k2⟩
    · rintro ⟨z, -, k1, k2⟩
      exact ⟨by simpa [extLin] using k1, by simpa [extLin] using k2⟩
  · let B : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) :=
      { toFun := fun z _ => z 0 + z 1
        map_add' := by intro x y; funext i; simp; ring
        map_smul' := by intro c x; funext i; simp; ring }
    refine isEF_compose (Z := Fin 2) (Q := Fin 1) _ _ _ r₁ r₂ h₁ h₂ 0 B (fun _ => 1)
      (extLin M M₁) (extraLin M M₁ 0) (extLin M M₂) (extraLin M M₂ 1) ?_
    intro x
    rw [poly_twoSum hcs ha hl1 hl2]
    simp only [extLin_add]
    constructor
    · rintro ⟨y, y', hyy, k1, k2⟩
      refine ⟨![y, y'], ?_, by simpa using k1, by simpa using k2⟩
      funext i; simp [B, hyy]
    · rintro ⟨z, hz, k1, k2⟩
      refine ⟨z 0, z 1, ?_, k1, k2⟩
      have := congrFun hz 0
      simpa [B] using this

end Final

end RMXCAux

theorem solution (α : Type) (M M₁ M₂ : Matroid α) [Fintype M.E] [Fintype M₁.E] [Fintype M₂.E]
    (hsum : RegMatroidXC.Main.IsOneSum M M₁ M₂ ∨ RegMatroidXC.Main.IsTwoSum M M₁ M₂) (r₁ r₂ : ℕ)
    (h₁ : IsEFOfSize (RegMatroidXC.Main.indepPolytope M₁) r₁)
    (h₂ : IsEFOfSize (RegMatroidXC.Main.indepPolytope M₂) r₂) :
    ∃ r : ℕ, IsEFOfSize (RegMatroidXC.Main.indepPolytope M) r ∧ r ≤ r₁ + r₂ :=
  RMXCAux.lemma3_aux M M₁ M₂ hsum r₁ r₂ h₁ h₂
