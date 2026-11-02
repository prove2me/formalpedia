-- Prove2me | solution 1 for RegMatroidXC.Main.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T11:41:04.612542+00:00
-- url     : https://prove2.me/submissions/9437191f-6faa-4338-83ec-74e4fd3d9e5c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_RegMatroidXC_Main_Matroids
import Definitions.Def_RegMatroidXC_Main_Sums
import Theorems.Thm_RegMatroidXC_Main_wong_martin_bound
import Theorems.Thm_RegMatroidXC_Main_trivial_bound
import Theorems.Thm_RegMatroidXC_Main_lemma_3
import Theorems.Thm_RegMatroidXC_Main_lemma_4
import Theorems.Thm_RegMatroidXC_Main_lemma_5
import Theorems.Thm_RegMatroidXC_Main_regular_sum_parts
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

theorem efUniv0 : IsEFOfSize (Set.univ : Set (Fin 0 → ℝ)) 0 :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, fun x => by simp⟩

/-- EF of a set described by equations and one polytope. -/
theorem isEF_preimage {ι ι1 Q : Type*} [Fintype ι] [Fintype ι1] [Fintype Q]
    (P : Set (ι → ℝ)) (P1 : Set (ι1 → ℝ)) (r : ℕ) (h1 : IsEFOfSize P1 r)
    (A : (ι → ℝ) →ₗ[ℝ] (Q → ℝ)) (b : Q → ℝ) (L : (ι → ℝ) →ₗ[ℝ] (ι1 → ℝ))
    (hP : ∀ x, x ∈ P ↔ A x = b ∧ L x ∈ P1) : IsEFOfSize P r := by
  have := isEF_compose (Z := Fin 0) (ι2 := Fin 0) P P1 Set.univ r 0 h1 efUniv0 A 0 b L 0 0 0
    (by intro x; rw [hP]; simp)
  simpa using this

theorem card_eq_ncard {α : Type*} (s : Set α) [Fintype s] : Fintype.card s = s.ncard := by
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

section Transfer

variable {α β : Type}

theorem regular_transfer (M : Matroid α) (M' : Matroid β) (g : M'.E → M.E)
    (hg : Function.Injective g)
    (hI : ∀ I ⊆ M'.E, M'.Indep I ↔ M.Indep (Subtype.val '' (g '' {x : M'.E | (x : β) ∈ I})))
    (hreg : IsRegular M) : IsRegular M' := by
  obtain ⟨m, A, hTU, hrep⟩ := hreg
  refine ⟨m, A.submatrix id g, hTU.submatrix id g, fun I => ?_⟩
  by_cases hIE : I ⊆ M'.E
  · rw [hI I hIE, hrep]
    have hsub : Subtype.val '' (g '' {x : M'.E | (x : β) ∈ I}) ⊆ M.E := by
      rintro _ ⟨x, _, rfl⟩; exact x.2
    have hset : {e : M.E | (e : α) ∈ Subtype.val '' (g '' {x : M'.E | (x : β) ∈ I})} =
        g '' {x : M'.E | (x : β) ∈ I} := by
      ext e
      simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · rintro ⟨y, hy, hye⟩; exact (Subtype.ext hye) ▸ hy
      · intro he; exact ⟨e, he, rfl⟩
    rw [hset]
    constructor
    · rintro ⟨-, h⟩
      exact ⟨hIE, h.comp_of_image hg.injOn⟩
    · rintro ⟨-, h⟩
      exact ⟨hsub, LinearIndepOn.image_of_comp g _ h⟩
  · constructor
    · intro h; exact absurd h.subset_ground hIE
    · rintro ⟨h, -⟩; exact absurd h hIE

/-- moving a matroid to a bigger (infinite) type -/
theorem map_transfer (M : Matroid α) [Fintype M.E] :
    ∃ (M' : Matroid (α ⊕ ℕ)) (_ : Fintype M'.E), Fintype.card M'.E = Fintype.card M.E ∧
      (IsRegular M → IsRegular M') ∧
      ∀ r, IsEFOfSize (indepPolytope M') r → IsEFOfSize (indepPolytope M) r := by
  classical
  let f : α → α ⊕ ℕ := Sum.inl
  have hf : Function.Injective f := Sum.inl_injective
  let M' := M.map f hf.injOn
  let φ : M.E ≃ M'.E := Equiv.Set.image f M.E hf
  have hφ : ∀ e, ((φ e : M'.E) : α ⊕ ℕ) = f e := fun e => rfl
  have hφs : ∀ x : M'.E, (x : α ⊕ ℕ) = f (φ.symm x) := by
    intro x; rw [← hφ, Equiv.apply_symm_apply]
  letI : Fintype M'.E := Fintype.ofEquiv _ φ
  refine ⟨M', this, Fintype.card_congr φ.symm, fun hreg => ?_, fun r hr => ?_⟩
  · refine regular_transfer M M' φ.symm φ.symm.injective (fun I hIE => ?_) hreg
    set J := Subtype.val '' (φ.symm '' {x : M'.E | (x : α ⊕ ℕ) ∈ I}) with hJ
    have himg : f '' J = I := by
      ext b; constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        obtain ⟨y, hy, rfl⟩ := hx
        have := hφs y; simp only [Set.mem_setOf_eq] at hy; rw [← this]; exact hy
      · intro hb
        refine ⟨_, ⟨φ.symm ⟨b, hIE hb⟩, ⟨⟨b, hIE hb⟩, hb, rfl⟩, rfl⟩, ?_⟩
        exact (hφs ⟨b, hIE hb⟩).symm
    rw [Matroid.map_indep_iff]
    constructor
    · rintro ⟨I₀, hI₀, rfl⟩
      have : I₀ = J := (Set.image_injective.2 hf) himg.symm
      rw [← this]; exact hI₀
    · intro hJi; exact ⟨J, hJi, himg.symm⟩
  · -- polytope relation
    have hchi : ∀ J : Set α, (fun x : M'.E => chi M J (φ.symm x)) = chi M' (f '' J) := by
      intro J; funext x
      simp only [chi]
      rw [hφs x, Set.indicator_image hf]
      rfl
    have hpoly : ∀ x : M.E → ℝ, x ∈ indepPolytope M ↔
        (fun y => x (φ.symm y)) ∈ indepPolytope M' := by
      intro x
      rw [mem_indepPolytope_iff, mem_indepPolytope_iff]
      constructor
      · rintro ⟨ι, _, w, J, hw0, hw1, hJ, rfl⟩
        refine ⟨ι, inferInstance, w, fun i => f '' J i, hw0, hw1,
          fun i => (hJ i).map f hf.injOn, ?_⟩
        funext y
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← hchi]
      · rintro ⟨ι, _, w, J, hw0, hw1, hJ, hx⟩
        have hJ' : ∀ i, ∃ I₀, M.Indep I₀ ∧ J i = f '' I₀ := fun i => (hJ i)
        choose I₀ hI₀ hJI using hJ'
        refine ⟨ι, inferInstance, w, I₀, hw0, hw1, hI₀, ?_⟩
        funext e
        have := congrFun hx (φ e)
        simp only [Equiv.symm_apply_apply, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul] at this
        rw [this, Finset.sum_apply]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hJI i, ← hchi]
        simp
    refine isEF_preimage (Q := Fin 0) _ _ r hr 0 0 (LinearMap.funLeft ℝ ℝ φ.symm) ?_
    intro x
    rw [hpoly]
    simp [LinearMap.funLeft]
    rfl

/-- deleting a loop -/
theorem delete_loop_transfer (M : Matroid α) [Fintype M.E] (e : α) (he : M.IsLoop e) :
    ∃ (M' : Matroid α) (_ : Fintype M'.E), Fintype.card M'.E + 1 = Fintype.card M.E ∧
      (IsRegular M → IsRegular M') ∧
      ∀ r, IsEFOfSize (indepPolytope M') r → IsEFOfSize (indepPolytope M) r := by
  classical
  have heE : e ∈ M.E := he.mem_ground
  let M' := M.delete {e}
  have hsub : M'.E ⊆ M.E := Set.diff_subset
  let g : M'.E → M.E := Set.inclusion hsub
  have hg : Function.Injective g := Set.inclusion_injective hsub
  letI : Fintype M'.E := Set.fintypeSubset _ hsub
  have hind : ∀ I ⊆ M'.E, M'.Indep I ↔ M.Indep I := by
    intro I hI
    rw [Matroid.delete_indep_iff]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, Set.disjoint_singleton_right.2 (fun heI => ?_)⟩
      exact (hI heI).2 rfl
  refine ⟨M', this, ?_, fun hreg => ?_, fun r hr => ?_⟩
  · rw [card_eq_ncard, card_eq_ncard]
    simp only [M', Matroid.delete_ground]
    rw [Set.ncard_diff_singleton_of_mem heE]
    have : 0 < M.E.ncard := (Set.ncard_pos M.E.toFinite).2 ⟨e, heE⟩
    omega
  · refine regular_transfer M M' g hg (fun I hIE => ?_) hreg
    have : Subtype.val '' (g '' {x : M'.E | (x : α) ∈ I}) = I := by
      ext a; constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact hx
      · intro ha; exact ⟨g ⟨a, hIE ha⟩, ⟨⟨a, hIE ha⟩, ha, rfl⟩, rfl⟩
    rw [this]; exact hind I hIE
  · have hpoly : ∀ x : M.E → ℝ, x ∈ indepPolytope M ↔
        x ⟨e, heE⟩ = 0 ∧ (fun y => x (g y)) ∈ indepPolytope M' := by
      intro x
      constructor
      · intro hx
        let R : Set (M.E → ℝ) := {x | x ⟨e, heE⟩ = 0 ∧ (fun y => x (g y)) ∈ indepPolytope M'}
        have hR : Convex ℝ R := by
          rintro x1 ⟨h11, h12⟩ x2 ⟨h21, h22⟩ a b ha hb hab
          refine ⟨by simp [h11, h21], ?_⟩
          have := (convex_convexHull ℝ _) h12 h22 ha hb hab
          have e : (fun y => (a • x1 + b • x2) (g y)) =
              (a • fun y => x1 (g y)) + b • fun y => x2 (g y) := by
            funext y; simp
          rw [e]; exact this
        refine convexHull_min ?_ hR hx
        rintro x ⟨I, hI, hxI⟩
        have hx : x = chi M I := funext hxI
        subst hx
        refine ⟨?_, ?_⟩
        · simp [chi, Set.indicator, he.notMem_of_indep hI]
        · have hI' : M'.Indep I := (Matroid.delete_indep_iff).2
            ⟨hI, Set.disjoint_singleton_right.2 (he.notMem_of_indep hI)⟩
          have : (fun y => chi M I (g y)) = chi M' I := by funext y; rfl
          rw [this]; exact chi_mem _ hI'
      · rintro ⟨h0, h1⟩
        obtain ⟨ι, _, w, J, hw0, hw1, hJ, hx⟩ := (mem_indepPolytope_iff _ _).1 h1
        rw [mem_indepPolytope_iff]
        refine ⟨ι, inferInstance, w, J, hw0, hw1,
          fun i => ((hind _ (hJ i).subset_ground).1 (hJ i)), ?_⟩
        funext y
        by_cases hy : (y : α) = e
        · have hy' : y = ⟨e, heE⟩ := Subtype.ext hy
          subst hy'
          rw [h0, Finset.sum_apply]
          symm
          apply Finset.sum_eq_zero
          intro i _
          have : e ∉ J i := fun h' => ((hJ i).subset_ground h').2 rfl
          simp [chi, Set.indicator, this]
        · have hyM : (y : α) ∈ M'.E := ⟨y.2, hy⟩
          have := congrFun hx ⟨y, hyM⟩
          have hgy : g ⟨y, hyM⟩ = y := rfl
          simp only [hgy] at this
          rw [this, Finset.sum_apply, Finset.sum_apply]
          rfl
    refine isEF_preimage (Q := Unit) _ _ r hr
      { toFun := fun x _ => x ⟨e, heE⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      0 (LinearMap.funLeft ℝ ℝ g) ?_
    intro x
    rw [hpoly]
    constructor
    · rintro ⟨h0, h1⟩; exact ⟨funext fun _ => h0, h1⟩
    · rintro ⟨h0, h1⟩; exact ⟨congrFun h0 (), h1⟩

end Transfer

theorem ef_empty {α : Type} (M : Matroid α) [Fintype M.E] (h : Fintype.card M.E = 0) :
    IsEFOfSize (indepPolytope M) 0 := by
  haveI : IsEmpty M.E := Fintype.card_eq_zero_iff.1 h
  refine ⟨0, 0, 0, 0, 0, 0, 0, 0, fun x => ?_⟩
  have hx : x = chi M ∅ := funext fun e => isEmptyElim e
  rw [hx]
  simp only [Matrix.zero_mulVec, add_zero, le_refl, and_self, exists_const, iff_true]
  exact chi_mem _ M.empty_indep

/-! ### arithmetic -/

theorem arith_two (n n1 n2 : ℝ) (h : n1 + n2 = n + 2) (h1 : 3 ≤ n1) (h2 : 3 ≤ n2) :
    n1 ^ 6 + n2 ^ 6 ≤ n ^ 6 := by
  have hb1 : n1 ≤ n - 1 := by linarith
  have hb2 : n2 ≤ n - 1 := by linarith
  set m := n - 1 with hm
  have hm0 : 0 ≤ m := by linarith
  have e1 : n1 ^ 6 ≤ m ^ 5 * n1 := by
    have : n1 ^ 5 ≤ m ^ 5 := pow_le_pow_left₀ (by linarith) hb1 5
    nlinarith
  have e2 : n2 ^ 6 ≤ m ^ 5 * n2 := by
    have : n2 ^ 5 ≤ m ^ 5 := pow_le_pow_left₀ (by linarith) hb2 5
    nlinarith
  have hn : n = m + 1 := by rw [hm]; ring
  have : m ^ 5 * (n1 + n2) = m ^ 5 * (m + 3) := by rw [h, hn]; ring
  have hpos : 0 ≤ 3 * m ^ 5 + 15 * m ^ 4 + 20 * m ^ 3 + 15 * m ^ 2 + 6 * m + 1 := by positivity
  have hexp : (m + 1) ^ 6 = m ^ 5 * (m + 3) + (3 * m ^ 5 + 15 * m ^ 4 + 20 * m ^ 3 +
      15 * m ^ 2 + 6 * m + 1) := by ring
  rw [hn, hexp]
  nlinarith

theorem arith_star (n c0 C1 S6 Ssum r0 : ℝ) (hn : 300 ≤ n) (hC1 : 0 ≤ C1) (hc : C1 ≤ c0)
    (h6 : S6 ≤ (n / 2 + 3) ^ 5 * Ssum) (hsum : Ssum ≤ 7 * n / 4)
    (hr : r0 ≤ C1 * n ^ 2 + 16 * (c0 * S6)) : r0 ≤ c0 * n ^ 6 := by
  have hc0 : 0 ≤ c0 := hC1.trans hc
  have hn0 : 0 ≤ n := by linarith
  have ha : n / 2 + 3 ≤ (51 / 100) * n := by linarith
  have ha5 : (n / 2 + 3) ^ 5 ≤ ((51 / 100) * n) ^ 5 := pow_le_pow_left₀ (by linarith) ha 5
  have hS : S6 ≤ ((51 / 100) * n) ^ 5 * (7 * n / 4) := by
    calc S6 ≤ (n / 2 + 3) ^ 5 * Ssum := h6
      _ ≤ (n / 2 + 3) ^ 5 * (7 * n / 4) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ ((51 / 100) * n) ^ 5 * (7 * n / 4) :=
          mul_le_mul_of_nonneg_right ha5 (by positivity)
  have hS' : 16 * S6 ≤ (97 / 100) * n ^ 6 := by
    have : ((51 / 100) * n) ^ 5 * (7 * n / 4) = (51 / 100) ^ 5 * (7 / 4) * n ^ 6 := by ring
    rw [this] at hS
    have hk : (51 / 100 : ℝ) ^ 5 * (7 / 4) * 16 ≤ 97 / 100 := by norm_num
    have hn6 : 0 ≤ n ^ 6 := by positivity
    nlinarith
  have hn2 : n ^ 2 ≤ (3 / 100) * n ^ 6 := by
    have : 100 ≤ n ^ 4 := by
      have : (300 : ℝ) ^ 4 ≤ n ^ 4 := pow_le_pow_left₀ (by norm_num) hn 4
      nlinarith
    have hn2' : 0 ≤ n ^ 2 := by positivity
    have : n ^ 6 = n ^ 2 * n ^ 4 := by ring
    nlinarith
  calc r0 ≤ C1 * n ^ 2 + 16 * (c0 * S6) := hr
    _ ≤ c0 * ((3 / 100) * n ^ 6) + c0 * ((97 / 100) * n ^ 6) := by
        have h1 : C1 * n ^ 2 ≤ c0 * ((3 / 100) * n ^ 6) := by
          have := mul_le_mul_of_nonneg_right hc (by positivity : (0:ℝ) ≤ n ^ 2)
          have h2 := mul_le_mul_of_nonneg_left hn2 hc0
          linarith
        have h2 : 16 * (c0 * S6) ≤ c0 * ((97 / 100) * n ^ 6) := by
          have := mul_le_mul_of_nonneg_left hS' hc0
          linarith
        linarith
    _ = c0 * n ^ 6 := by ring

end RMXCAux

open RegMatroidXC.Main RMXCAux in
theorem solution : ∃ c₀ : ℝ, ∀ (α : Type) (M : Matroid α) [Fintype M.E], IsRegular M →
    ∃ r : ℕ, IsEFOfSize (indepPolytope M) r ∧ (r : ℝ) ≤ c₀ * (Fintype.card M.E : ℝ) ^ 6 := by
  classical
  obtain ⟨cw, hcw⟩ := RegMatroidXC.Main.wong_martin_bound
  obtain ⟨c1, hc1⟩ := RegMatroidXC.Main.lemma_5
  set C1 : ℝ := max c1 0 with hC1def
  set c0 : ℝ := max ((2 : ℝ) ^ 300) (max (max cw 0) C1) with hc0def
  have hc0pos : 0 ≤ c0 := le_trans (by positivity) (le_max_left _ _)
  have hcwle : max cw 0 ≤ c0 := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC1le : C1 ≤ c0 := le_trans (le_max_right _ _) (le_max_right _ _)
  have h2le : (2 : ℝ) ^ 300 ≤ c0 := le_max_left _ _
  have key : ∀ n : ℕ, ∀ (β : Type) [Infinite β] (M : Matroid β) [Fintype M.E],
      Fintype.card M.E = n → IsRegular M →
      ∃ r : ℕ, IsEFOfSize (indepPolytope M) r ∧ (r : ℝ) ≤ c0 * (n : ℝ) ^ 6 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro β _ M _ hcard hreg
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0; exact ⟨0, ef_empty M hcard, by simp⟩
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    by_cases hsmall : n < 300
    · obtain ⟨r, hr, hrle⟩ := trivial_bound β M
      refine ⟨r, hr, ?_⟩
      have h1 : (r : ℝ) ≤ 2 ^ n := by rw [← hcard]; exact_mod_cast hrle
      have h2 : (2 : ℝ) ^ n ≤ 2 ^ 300 := pow_le_pow_right₀ (by norm_num) hsmall.le
      have h3 : (1 : ℝ) ≤ (n : ℝ) ^ 6 := one_le_pow₀ hn1
      nlinarith
    push Not at hsmall
    have hnR : (300 : ℝ) ≤ n := by exact_mod_cast hsmall
    -- loops
    by_cases hloop : ∃ e, M.IsLoop e
    · obtain ⟨e, he⟩ := hloop
      obtain ⟨M', inst', hc', hreg', hef⟩ := delete_loop_transfer M e he
      obtain ⟨r, hr, hrle⟩ := ih (n - 1) (by omega) β M' (by omega) (hreg' hreg)
      refine ⟨r, hef r hr, le_trans hrle ?_⟩
      have : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) this 6) hc0pos
    push Not at hloop
    have hll : M.Loopless := Matroid.loopless_iff_forall_not_isLoop.2 (fun e _ => hloop e)
    -- graphic or cographic
    by_cases hgc : IsGraphic M ∨ IsCographic M
    · obtain ⟨r, hr, hrle⟩ := hcw β M hgc
      refine ⟨r, hr, ?_⟩
      rw [hcard] at hrle
      have hn2 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 6 := pow_le_pow_right₀ hn1 (by norm_num)
      calc (r : ℝ) ≤ cw * (n : ℝ) ^ 2 := hrle
        _ ≤ max cw 0 * (n : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ c0 * (n : ℝ) ^ 6 := mul_le_mul hcwle hn2 (by positivity) hc0pos
    push Not at hgc
    -- R10
    by_cases hR10 : IsR10 M
    · exfalso
      obtain ⟨f, hbij, -⟩ := hR10
      have h10 : M.E.ncard = 10 := by
        rw [← hbij.injOn.ncard_image, hbij.image_eq, Set.ncard_univ, Nat.card_eq_fintype_card,
          Fintype.card_fin]
      rw [card_eq_ncard] at hcard; omega
    -- 1-sums
    by_cases h1 : ∃ M₁ M₂, IsOneSum M M₁ M₂
    · obtain ⟨M₁, M₂, hs⟩ := h1
      obtain ⟨hr1, hr2⟩ := regular_sum_parts β M M₁ M₂ hreg (Or.inl hs)
      have hs' := hs
      obtain ⟨-, -, hcs, hd, hne1, hne2⟩ := hs
      have hEu : M.E = M₁.E ∪ M₂.E := by rw [hcs.1]; exact hd.symmDiff_eq_sup
      have hf1 : M₁.E.Finite := M.E.toFinite.subset (hEu ▸ Set.subset_union_left)
      have hf2 : M₂.E.Finite := M.E.toFinite.subset (hEu ▸ Set.subset_union_right)
      letI := hf1.fintype
      letI := hf2.fintype
      have hsz : M₁.E.ncard + M₂.E.ncard = n := by
        rw [← Set.ncard_union_eq hd hf1 hf2, ← hEu, ← card_eq_ncard, hcard]
      have hp1 : 0 < M₁.E.ncard := (Set.ncard_pos hf1).2 hne1
      have hp2 : 0 < M₂.E.ncard := (Set.ncard_pos hf2).2 hne2
      obtain ⟨r1, hr1', hb1⟩ := ih M₁.E.ncard (by omega) β M₁ (card_eq_ncard _) hr1
      obtain ⟨r2, hr2', hb2⟩ := ih M₂.E.ncard (by omega) β M₂ (card_eq_ncard _) hr2
      obtain ⟨r, hr, hrle⟩ := lemma_3 β M M₁ M₂ (Or.inl hs') r1 r2 hr1' hr2'
      refine ⟨r, hr, ?_⟩
      have hszR : (M₁.E.ncard : ℝ) + M₂.E.ncard = n := by exact_mod_cast hsz
      have hpow : (M₁.E.ncard : ℝ) ^ 6 + (M₂.E.ncard : ℝ) ^ 6 ≤ (n : ℝ) ^ 6 := by
        rw [← hszR]; exact pow_add_pow_le (by positivity) (by positivity) (by norm_num)
      calc (r : ℝ) ≤ r1 + r2 := by exact_mod_cast hrle
        _ ≤ c0 * (M₁.E.ncard : ℝ) ^ 6 + c0 * (M₂.E.ncard : ℝ) ^ 6 := add_le_add hb1 hb2
        _ ≤ c0 * (n : ℝ) ^ 6 := by rw [← mul_add]; exact mul_le_mul_of_nonneg_left hpow hc0pos
    push Not at h1
    -- 2-sums
    by_cases h2 : ∃ M₁ M₂, IsTwoSum M M₁ M₂
    · obtain ⟨M₁, M₂, hs⟩ := h2
      obtain ⟨hr1, hr2⟩ := regular_sum_parts β M M₁ M₂ hreg (Or.inr hs)
      have hs' := hs
      obtain ⟨-, -, hcs, a, ha, -, -, -, -, h31, h32⟩ := hs
      have haE : a ∈ M₁.E ∩ M₂.E := by rw [ha]; rfl
      have haM : a ∉ M.E := by
        rw [hcs.1]; rintro (⟨-, h⟩ | ⟨-, h⟩)
        · exact h haE.2
        · exact h haE.1
      have hU : M₁.E ∪ M₂.E = insert a M.E := by
        ext e
        rw [hcs.1]
        constructor
        · rintro (h | h)
          · by_cases h' : e ∈ M₂.E
            · have : e ∈ M₁.E ∩ M₂.E := ⟨h, h'⟩
              rw [ha] at this; exact Or.inl this
            · exact Or.inr (Or.inl ⟨h, h'⟩)
          · by_cases h' : e ∈ M₁.E
            · have : e ∈ M₁.E ∩ M₂.E := ⟨h', h⟩
              rw [ha] at this; exact Or.inl this
            · exact Or.inr (Or.inr ⟨h, h'⟩)
        · rintro (h | (⟨h, -⟩ | ⟨h, -⟩))
          · rw [h]; exact Or.inl haE.1
          · exact Or.inl h
          · exact Or.inr h
      have hfin : (insert a M.E).Finite := M.E.toFinite.insert a
      have hf1 : M₁.E.Finite := hfin.subset (hU ▸ Set.subset_union_left)
      have hf2 : M₂.E.Finite := hfin.subset (hU ▸ Set.subset_union_right)
      letI := hf1.fintype
      letI := hf2.fintype
      have hsz : M₁.E.ncard + M₂.E.ncard = n + 2 := by
        rw [← Set.ncard_union_add_ncard_inter _ _ hf1 hf2, hU, ha, Set.ncard_singleton,
          Set.ncard_insert_of_notMem haM, ← card_eq_ncard, hcard]
      obtain ⟨r1, hr1', hb1⟩ := ih M₁.E.ncard (by omega) β M₁ (card_eq_ncard _) hr1
      obtain ⟨r2, hr2', hb2⟩ := ih M₂.E.ncard (by omega) β M₂ (card_eq_ncard _) hr2
      obtain ⟨r, hr, hrle⟩ := lemma_3 β M M₁ M₂ (Or.inr hs') r1 r2 hr1' hr2'
      refine ⟨r, hr, ?_⟩
      have hszR : (M₁.E.ncard : ℝ) + M₂.E.ncard = n + 2 := by exact_mod_cast hsz
      have hpow := arith_two n _ _ hszR (by exact_mod_cast h31) (by exact_mod_cast h32)
      calc (r : ℝ) ≤ r1 + r2 := by exact_mod_cast hrle
        _ ≤ c0 * (M₁.E.ncard : ℝ) ^ 6 + c0 * (M₂.E.ncard : ℝ) ^ 6 := add_le_add hb1 hb2
        _ ≤ c0 * (n : ℝ) ^ 6 := by rw [← mul_add]; exact mul_le_mul_of_nonneg_left hpow hc0pos
    push Not at h2
    -- 3-connected case: star decomposition
    obtain ⟨k, M₀, Ms, hk1, hk4, hgc0, hn0le, hregs, hsize, hsd, htv⟩ :=
      lemma_4 β M hreg hgc.1 hgc.2 hR10 h1 h2
    have hsd' := hsd
    obtain ⟨h0fin, hfin, hdisj, hpair, hE, -⟩ := hsd
    letI : Fintype M₀.E := h0fin.fintype
    letI : ∀ i, Fintype (Ms i).E := fun i => (hfin i).fintype
    rw [hcard] at hk4 hn0le hsize
    have hlt : ∀ i, (Ms i).E.ncard < n := by
      intro i
      have h := hsize i
      have : ((Ms i).E.ncard : ℝ) < n := by linarith
      exact_mod_cast this
    have hpart : ∀ i, ∃ r, IsEFOfSize (indepPolytope (Ms i)) r ∧
        (r : ℝ) ≤ c0 * ((Ms i).E.ncard : ℝ) ^ 6 :=
      fun i => ih _ (hlt i) β (Ms i) (card_eq_ncard _) (hregs i)
    choose r hr hrb using hpart
    obtain ⟨r0, hr0, hr0b⟩ := hc1 β M M₀ k Ms hll hgc0 hregs hsd' htv r hr
    refine ⟨r0, hr0, ?_⟩
    -- counting
    let D : Fin k → Set β := fun i => (Ms i).E \ M₀.E
    have hDsub : ∀ i, D i ⊆ M.E := by
      intro i e ⟨he, he0⟩
      rw [hE]
      refine ⟨Or.inr (Set.mem_iUnion.2 ⟨i, he⟩), fun h' => ?_⟩
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 h'
      exact he0 hj.1
    have hDfin : ∀ i, Finite (D i) := fun i => ((hfin i).subset Set.diff_subset).to_subtype
    have hDcard : ∑ i, (D i).ncard ≤ n := by
      have hinj : Function.Injective (fun x : (Σ i, D i) => (⟨x.2, hDsub x.1 x.2.2⟩ : M.E)) := by
        rintro ⟨i, x⟩ ⟨j, y⟩ hxy
        simp only [Subtype.mk.injEq] at hxy
        by_cases hij : i = j
        · subst hij
          have : x = y := Subtype.ext hxy
          rw [this]
        · exfalso
          exact Set.disjoint_left.1 (hdisj hij) x.2.1 (hxy ▸ y.2.1)
      have := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_sigma] at this
      simp_rw [Nat.card_coe_set_eq] at this
      rw [← card_eq_ncard, hcard] at this
      exact this
    have hni : ∀ i, (Ms i).E.ncard = (D i).ncard + 3 := by
      intro i
      have h3 := (hpair i).2.2.1
      have := Set.ncard_inter_add_ncard_diff_eq_ncard (Ms i).E M₀.E (hfin i)
      rw [Set.inter_comm, h3] at this
      simp only [D]
      omega
    have hsumN : ∑ i, (Ms i).E.ncard ≤ n + 3 * k := by
      simp_rw [hni]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      omega
    have hsum : (∑ i, ((Ms i).E.ncard : ℝ)) ≤ 7 * n / 4 := by
      have : (∑ i, ((Ms i).E.ncard : ℝ)) ≤ n + 3 * k := by exact_mod_cast hsumN
      linarith
    refine arith_star n c0 C1 (∑ i, ((Ms i).E.ncard : ℝ) ^ 6) (∑ i, ((Ms i).E.ncard : ℝ)) r0 hnR
      (le_max_right _ _) hC1le ?_ hsum ?_
    · rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      have h0 : (0 : ℝ) ≤ (Ms i).E.ncard := by positivity
      have h5 : ((Ms i).E.ncard : ℝ) ^ 5 ≤ (n / 2 + 3) ^ 5 := pow_le_pow_left₀ h0 (hsize i) 5
      have : ((Ms i).E.ncard : ℝ) ^ 6 = ((Ms i).E.ncard : ℝ) ^ 5 * (Ms i).E.ncard := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right h5 h0
    · have hm0 : (Fintype.card M₀.E : ℝ) ≤ n := by rw [card_eq_ncard]; exact hn0le
      have hm0' : (0 : ℝ) ≤ Fintype.card M₀.E := by positivity
      have hA : c1 * (Fintype.card M₀.E : ℝ) ^ 2 ≤ C1 * (n : ℝ) ^ 2 := by
        calc c1 * (Fintype.card M₀.E : ℝ) ^ 2 ≤ C1 * (Fintype.card M₀.E : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          _ ≤ C1 * (n : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0' hm0 2) (le_max_right _ _)
      have hB : (∑ i, (r i : ℝ)) ≤ c0 * ∑ i, ((Ms i).E.ncard : ℝ) ^ 6 := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun i _ => hrb i)
      linarith
  refine ⟨c0, fun α M _ hreg => ?_⟩
  obtain ⟨M', inst', hc', hreg', hef⟩ := map_transfer M
  obtain ⟨r, hr, hrle⟩ := key _ (α ⊕ ℕ) M' rfl (hreg' hreg)
  exact ⟨r, hef r hr, by rw [← hc']; exact hrle⟩
