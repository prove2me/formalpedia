-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P11.resolvent_order_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:16:52.901084+00:00
-- url     : https://prove2.me/submissions/31c934f3-6c0f-4d87-9903-f3d581972951

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P11

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter
open QAlgorithms.Papers.Independent.Next46.P06
open QAlgorithms.Papers.Independent.Renew46.P11
open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore restrictGraph)

namespace X6P11R

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma mem_add_id (A : Graph X) (x y : X) :
    (x, y) ∈ graphAdd identityGraph A ↔ (x, y - x) ∈ A := by
  simp only [graphAdd, identityGraph, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    rw [ha]; simpa using hb
  · intro h; exact ⟨x, y - x, rfl, h, by abel⟩

lemma mem_shift (A : Graph X) (x y : X) :
    (x, y) ∈ banachResolventShift A (-1) ↔ (x, -y - x) ∈ A := by
  simp only [banachResolventShift, graphAdd, graphScale, identityGraph, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, b, ⟨a', ha', rfl⟩, ⟨b', hb', rfl⟩, rfl⟩
    rw [ha']; simpa using hb'
  · intro h
    exact ⟨-x, -(-y - x), ⟨x, rfl, by simp⟩, ⟨-y - x, h, by simp⟩, by abel⟩

lemma bounded_inv (A : Graph X) (hA : Sectorial A) :
    Bounded (graphInverse (graphAdd identityGraph A)) := by
  obtain ⟨-, angle, h0, hpi, hsub, -⟩ := hA
  have hres : (-1 : ℂ) ∈ banachResolventSet A := by
    by_contra h
    have := hsub h
    rcases this with h1 | h1
    · norm_num at h1
    · rw [Complex.arg_neg_one, abs_of_pos Real.pi_pos] at h1; linarith
  obtain ⟨T, hT⟩ := hres
  refine ⟨-T, ?_⟩
  ext ⟨y, x⟩
  simp only [graphInverse, banachBoundedGraph, Set.mem_setOf_eq, mem_add_id,
    ContinuousLinearMap.neg_apply]
  have := Set.ext_iff.mp hT (-y, x)
  simp only [graphInverse, banachBoundedGraph, Set.mem_setOf_eq, mem_shift, map_neg] at this
  rw [← this]; simp

end X6P11R

open X6P11R in
theorem solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [CompleteSpace X] (A : Graph X) (hA : Sectorial A)
    (hdense : Dense (graphDomain A)) :
    graphMul A (graphInverse (graphAdd identityGraph A)) =
      banachBoundedGraph (ContinuousLinearMap.id ℂ X - onePlusInverse A) ∧
    graphMul (graphInverse (graphAdd identityGraph A)) A =
      restrictGraph (banachBoundedGraph (ContinuousLinearMap.id ℂ X - onePlusInverse A))
        (graphDomain A) ∧
    (¬ Bounded A → graphMul (graphInverse (graphAdd identityGraph A)) A ≠
      graphMul A (graphInverse (graphAdd identityGraph A))) := by
  have hB := bounded_inv A hA
  set R := onePlusInverse A
  have hR : graphInverse (graphAdd identityGraph A) = banachBoundedGraph R := by
    simp only [R, onePlusInverse, boundedValue, dif_pos hB]
    exact Classical.choose_spec hB
  have hRm : ∀ y x, (y, x) ∈ graphInverse (graphAdd identityGraph A) ↔ x = R y := by
    intro y x; rw [hR]; rfl
  -- (x, b) ∈ A ↔ x = R (x + b)
  have K : ∀ x b, (x, b) ∈ A ↔ x = R (x + b) := by
    intro x b
    rw [← hRm]
    simp only [graphInverse, Set.mem_setOf_eq, mem_add_id, add_sub_cancel_left]
  have hfun := hA.1.2.2.2.2
  have hlin := hA.1.2.2.1
  have hsm := hA.1.2.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · ext ⟨x, z⟩
    simp only [graphMul, banachBoundedGraph, Set.mem_setOf_eq, hRm,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    constructor
    · rintro ⟨y, rfl, hz⟩
      have h1 : (R x, x - R x) ∈ A := by rw [K]; simp
      exact hfun _ _ _ hz h1
    · rintro rfl
      exact ⟨R x, rfl, by rw [K]; simp⟩
  · ext ⟨x, z⟩
    simp only [graphMul, restrictGraph, banachBoundedGraph, Set.mem_setOf_eq, hRm,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, ⟨y, hy⟩⟩
      have h1 := (K x y).mp hy
      rw [map_add] at h1
      exact ((sub_eq_iff_eq_add').mpr h1).symm
    · rintro ⟨rfl, ⟨y, hy⟩⟩
      refine ⟨y, hy, ?_⟩
      have h1 := (K x y).mp hy
      rw [map_add] at h1
      exact (sub_eq_iff_eq_add').mpr h1
  · intro hnb heq
    -- domain of A is everything
    have hdom : ∀ x, ∃ y, (x, y) ∈ A := by
      intro x
      have : (x, x - R x) ∈ graphMul A (graphInverse (graphAdd identityGraph A)) :=
        ⟨R x, (hRm x (R x)).mpr rfl, by rw [K]; simp⟩
      rw [← heq] at this
      obtain ⟨y, hy, -⟩ := this
      exact ⟨y, hy⟩
    choose a ha using hdom
    have zero : (0 : X × X) ∈ A := hA.1.2.1
    let g : X →ₗ[ℂ] X :=
      { toFun := a
        map_add' := fun x y => hfun _ _ _ (ha (x + y)) (hlin _ _ _ _ (ha x) (ha y))
        map_smul' := fun c x => hfun _ _ _ (ha (c • x)) (hsm c _ _ (ha x)) }
    have hgA : A = {p | p.2 = g p.1} := by
      ext ⟨x, y⟩
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h; exact hfun _ _ _ h (ha x)
      · rintro rfl; exact ha x
    have hcl : IsClosed (g.graph : Set (X × X)) := by
      have : (g.graph : Set (X × X)) = A := by
        rw [hgA]; ext p; simp [LinearMap.mem_graph_iff]
      rw [this]; exact hA.1.1
    exact hnb ⟨⟨g, g.continuous_of_isClosed_graph hcl⟩, hgA⟩
