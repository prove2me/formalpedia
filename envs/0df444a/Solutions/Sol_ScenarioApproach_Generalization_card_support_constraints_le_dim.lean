-- Prove2me | solution 1 for ScenarioApproach.Generalization.card_support_constraints_le_dim
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:17:37.998635+00:00
-- url     : https://prove2.me/submissions/4a0ee530-2561-41f7-a8ba-0945eaea80d1

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_scenarioProgram
import Definitions.Def_ScenarioApproach_Generalization_supportConstraint



namespace ScenarioApproach.Generalization

theorem card_support_core {d m : ℕ} {Δ : Type*}
    (c : EuclideanSpace ℝ (Fin d)) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (hΘ_convex : Convex ℝ Θ) (hΘδ_convex : ∀ δ, Convex ℝ (Θδ δ))
    (ω : Fin m → Δ) (θstar : EuclideanSpace ℝ (Fin d)) (hθstar : IsSolution c Θ Θδ ω θstar) :
    numSupportConstraints c Θ Θδ ω θstar ≤ d := by
  classical
  by_contra hlt
  push Not at hlt
  unfold numSupportConstraints at hlt
  set S := (Finset.univ.filter fun i : Fin m => IsSupportConstraint c Θ Θδ ω θstar i) with hS
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (s := S) (n := d + 1) (by omega)
  let g : Fin (d + 1) → Fin m := fun j => ((T.equivFin.symm (Fin.cast hTcard.symm j)) : Fin m)
  have ginj : Function.Injective g := by
    intro a b hab
    have := Subtype.ext hab
    have := T.equivFin.symm.injective this
    exact Fin.cast_injective _ this
  have gS : ∀ j, IsSupportConstraint c Θ Θδ ω θstar (g j) := by
    intro j
    have h1 : g j ∈ S := hTS (T.equivFin.symm (Fin.cast hTcard.symm j)).2
    rw [hS, Finset.mem_filter] at h1
    exact h1.2
  choose θ hθΘ hθδ hθc using gS
  let p : Option (Fin (d + 1)) → EuclideanSpace ℝ (Fin d) := fun o =>
    match o with
    | none => θstar
    | some j => θ j
  have hfeas := hθstar.1
  have hstarΘ : θstar ∈ Θ := hfeas.1
  have hstarδ : ∀ l, θstar ∈ Θδ (ω l) := by
    intro l; exact Set.mem_iInter.mp hfeas.2 l
  have hnot : ¬ AffineIndependent ℝ p := by
    intro hai
    have := hai.card_le_finrank_succ
    have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range p))
    rw [finrank_euclideanSpace_fin] at h2
    simp at this
    omega
  obtain ⟨I, q, hq1, hq2⟩ := Convex.radon_partition hnot
  -- feasibility of q
  have hpΘ : ∀ o, p o ∈ Θ := by
    intro o; cases o with
    | none => exact hstarΘ
    | some j => exact hθΘ j
  have hqΘ : q ∈ Θ := (convexHull_min (by rintro _ ⟨o, -, rfl⟩; exact hpΘ o) hΘ_convex) hq1
  have hqδ : ∀ l, q ∈ Θδ (ω l) := by
    intro l
    by_cases hA : ∃ j, some j ∈ I ∧ g j = l
    · obtain ⟨j, hjI, hjl⟩ := hA
      refine (convexHull_min ?_ (hΘδ_convex _)) hq2
      rintro _ ⟨o, ho, rfl⟩
      cases o with
      | none => exact hstarδ l
      | some j' =>
        apply hθδ j' l
        intro h
        rw [← hjl] at h
        have := ginj h
        subst this
        exact ho hjI
    · push Not at hA
      refine (convexHull_min ?_ (hΘδ_convex _)) hq1
      rintro _ ⟨o, ho, rfl⟩
      cases o with
      | none => exact hstarδ l
      | some j' =>
        apply hθδ j' l
        intro h
        exact hA j' ho h.symm
  have hqfeas : q ∈ feasibleSet Θ Θδ ω := ⟨hqΘ, Set.mem_iInter.mpr hqδ⟩
  have hle := hθstar.2 q hqfeas
  -- cost of q
  have hconv : Convex ℝ {x : EuclideanSpace ℝ (Fin d) | inner ℝ c x < inner ℝ c θstar} :=
    convex_halfSpace_lt (f := fun x => inner ℝ c x) (innerₛₗ ℝ c).isLinear _
  have hlt' : inner ℝ c q < inner ℝ c θstar := by
    by_cases hn : none ∈ I
    · refine (convexHull_min ?_ hconv) hq2
      rintro _ ⟨o, ho, rfl⟩
      cases o with
      | none => exact absurd hn ho
      | some j => exact hθc j
    · refine (convexHull_min ?_ hconv) hq1
      rintro _ ⟨o, ho, rfl⟩
      cases o with
      | none => exact absurd ho hn
      | some j => exact hθc j
  linarith

end ScenarioApproach.Generalization

open ScenarioApproach.Generalization


theorem solution {d m : ℕ} {Δ : Type*}
    (c : EuclideanSpace ℝ (Fin d)) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (hΘ_convex : Convex ℝ Θ) (hΘδ_convex : ∀ δ, Convex ℝ (Θδ δ))
    (ω : Fin m → Δ) (θstar : EuclideanSpace ℝ (Fin d)) (hθstar : IsSolution c Θ Θδ ω θstar) :
    numSupportConstraints c Θ Θδ ω θstar ≤ d := by
  exact card_support_core c Θ Θδ hΘ_convex hΘδ_convex ω θstar hθstar
