-- Prove2me | solution 1 for OpenConnectedComponentPolygonallyConnectedBundled
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T23:53:05.103087+00:00
-- url     : https://prove2.me/submissions/ae96c3ec-2e50-4526-9add-73ce4828ab1d

import Mathlib
import Definitions.Def_PlaneFaceData
import Definitions.Def_PolygonallyPathConnected

set_option autoImplicit false

namespace OCCPC871

/-- Prepend a vertex `r` to a polygonal path, assuming the new segment lies in `C`. -/
theorem prepend (C : Set (EuclideanSpace ℝ (Fin 2))) (γ : PolygonalPath)
    (hγ : γ.carrier ⊆ C) (r : EuclideanSpace ℝ (Fin 2))
    (hseg : segment ℝ r γ.source ⊆ C) :
    ∃ γ' : PolygonalPath, γ'.source = r ∧ γ'.target = γ.target ∧ γ'.carrier ⊆ C := by
  have hne := γ.vertices_nonempty
  have hhead := γ.source_eq_head
  have hlast := γ.target_eq_last
  refine ⟨{ vertices := r :: γ.vertices
            vertices_nonempty := List.cons_ne_nil _ _
            source := r
            target := γ.target
            source_eq_head := rfl
            target_eq_last := ?_
            carrier := ({r, γ.target} : Set (EuclideanSpace ℝ (Fin 2))) ∪
              {p | ∃ i : ℕ, ∃ hi : i + 1 < (r :: γ.vertices).length,
                p ∈ segment ℝ (r :: γ.vertices)[i] (r :: γ.vertices)[i + 1]}
            carrier_eq := rfl }, rfl, rfl, ?_⟩
  · rw [List.getLast?_cons, hlast]
    simp
  · have hcar := γ.carrier_eq
    intro x hx
    rcases hx with hx | hx
    · rcases hx with hx | hx
      · subst hx; exact hseg (left_mem_segment ℝ _ _)
      · rw [Set.mem_singleton_iff] at hx; subst hx
        apply hγ; rw [hcar]; exact Or.inl (Or.inr rfl)
    · obtain ⟨i, hi, hx⟩ := hx
      cases i with
      | zero =>
        have h0 : γ.vertices[0]'(by simpa using hi) = γ.source := by
          rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by simpa using hi)] at hhead
          exact Option.some_injective _ hhead
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hx
        rw [h0] at hx
        exact hseg hx
      | succ j =>
        simp only [List.getElem_cons_succ] at hx
        apply hγ; rw [hcar]
        exact Or.inr ⟨j, by simpa using hi, hx⟩

theorem single (C : Set (EuclideanSpace ℝ (Fin 2))) (q : EuclideanSpace ℝ (Fin 2))
    (hq : q ∈ C) :
    ∃ γ : PolygonalPath, γ.source = q ∧ γ.target = q ∧ γ.carrier ⊆ C := by
  refine ⟨{ vertices := [q]
            vertices_nonempty := List.cons_ne_nil _ _
            source := q
            target := q
            source_eq_head := rfl
            target_eq_last := rfl
            carrier := ({q, q} : Set (EuclideanSpace ℝ (Fin 2))) ∪
              {p | ∃ i : ℕ, ∃ hi : i + 1 < [q].length,
                p ∈ segment ℝ [q][i] [q][i + 1]}
            carrier_eq := rfl }, rfl, rfl, ?_⟩
  intro x hx
  rcases hx with hx | hx
  · rcases hx with hx | hx
    · subst hx; exact hq
    · rw [Set.mem_singleton_iff] at hx; subst hx; exact hq
  · obtain ⟨i, hi, _⟩ := hx
    simp at hi

theorem comp_open (U C : Set (EuclideanSpace ℝ (Fin 2))) (hU : IsOpen U)
    (hC : ComplementComponent Uᶜ C) : IsOpen C := by
  obtain ⟨hne, hsub, hconn, hmax⟩ := hC
  rw [compl_compl] at hsub
  rw [Metric.isOpen_iff]
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x (hsub hx)
  refine ⟨ε, hε, ?_⟩
  have hb : IsConnected (Metric.ball x ε) :=
    ⟨Metric.nonempty_ball.2 hε, (convex_ball x ε).isPreconnected⟩
  have hu : IsConnected (C ∪ Metric.ball x ε) :=
    ⟨hne.mono Set.subset_union_left,
      hconn.isPreconnected.union x hx (Metric.mem_ball_self hε) hb.isPreconnected⟩
  have := hmax (C ∪ Metric.ball x ε) (hne.mono Set.subset_union_left)
    (by rw [compl_compl]; exact Set.union_subset hsub hball) hu Set.subset_union_left
  exact fun y hy => this (Or.inr hy)

end OCCPC871

theorem solution
    (U C : Set (EuclideanSpace ℝ (Fin 2))) :
    IsOpen U → ComplementComponent Uᶜ C → PolygonallyPathConnected C := by
  intro hU hC
  have hCo := OCCPC871.comp_open U C hU hC
  have hconn := hC.2.2.1
  intro p q hp hq
  let R : Set (EuclideanSpace ℝ (Fin 2)) :=
    {x | ∃ γ : PolygonalPath, γ.source = x ∧ γ.target = q ∧ γ.carrier ⊆ C}
  have hball : ∀ x ∈ C, ∃ ε > 0, Metric.ball x ε ⊆ C := fun x hx =>
    Metric.isOpen_iff.1 hCo x hx
  have hRo : IsOpen R := by
    rw [Metric.isOpen_iff]
    rintro x ⟨γ, hs, ht, hc⟩
    have hxC : x ∈ C := by
      rw [← hs]; apply hc; rw [γ.carrier_eq]; exact Or.inl (Or.inl rfl)
    obtain ⟨ε, hε, hb⟩ := hball x hxC
    refine ⟨ε, hε, fun y hy => ?_⟩
    obtain ⟨γ', h1, h2, h3⟩ := OCCPC871.prepend C γ hc y (by
      rw [hs]
      exact ((convex_ball x ε).segment_subset hy (Metric.mem_ball_self hε)).trans hb)
    exact ⟨γ', h1, h2.trans ht, h3⟩
  have hVo : IsOpen (C \ R) := by
    rw [Metric.isOpen_iff]
    rintro x ⟨hxC, hxR⟩
    obtain ⟨ε, hε, hb⟩ := hball x hxC
    refine ⟨ε, hε, fun y hy => ⟨hb hy, fun hyR => hxR ?_⟩⟩
    obtain ⟨γ, hs, ht, hc⟩ := hyR
    obtain ⟨γ', h1, h2, h3⟩ := OCCPC871.prepend C γ hc x (by
      rw [hs]
      exact ((convex_ball x ε).segment_subset (Metric.mem_ball_self hε) hy).trans hb)
    exact ⟨γ', h1, h2.trans ht, h3⟩
  have hsub : C ⊆ R := by
    apply hconn.isPreconnected.subset_left_of_subset_union hRo hVo
    · exact Set.disjoint_sdiff_right
    · intro x hx
      by_cases h : x ∈ R
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
    · exact ⟨q, hq, OCCPC871.single C q hq⟩
  obtain ⟨γ, hs, ht, hc⟩ := hsub hp
  exact ⟨γ, hs, ht, hc⟩
