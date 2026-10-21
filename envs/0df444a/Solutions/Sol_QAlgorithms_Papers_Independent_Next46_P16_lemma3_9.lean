-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P16.lemma3_9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:32:55.824645+00:00
-- url     : https://prove2.me/submissions/a4e02a0c-a257-4854-ab5c-7f4d995ec624

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P16
noncomputable section

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration)

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass)

open scoped BigOperators ENNReal ComplexOrder

open QAlgorithms.Papers.Independent.Next46.P16

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P16.canonicalComplexCalculus

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P16.canonicalRealCalculus

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P16.canonicalRealNonUnitalCalculus

theorem g62g_atom {n : ℕ} (A : CanonicalHilbert n →ₗ.[ℂ] CanonicalHilbert n)
    (hA : IsClosed (A.graph : Set (CanonicalHilbert n × CanonicalHilbert n)))
    (T : CanonicalOperator n) (hD : ∀ x, T x ∈ A.domain) :
    ∃ B : CanonicalOperator n, ∀ x y : CanonicalHilbert n,
      (T x, y) ∈ A.graph ↔ B x = y := by
  let L : CanonicalHilbert n →ₗ[ℂ] CanonicalHilbert n :=
    A.toFun.comp ((T : CanonicalHilbert n →ₗ[ℂ] CanonicalHilbert n).codRestrict A.domain hD)
  have hL : ∀ x y, (T x, y) ∈ A.graph ↔ L x = y := by
    intro x y
    rw [LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨z, hz1, hz2⟩
      have : z = ⟨T x, hD x⟩ := Subtype.ext hz1
      subst this
      exact hz2
    · intro h
      exact ⟨⟨T x, hD x⟩, rfl, h⟩
  have hg : IsClosed (L.graph : Set (CanonicalHilbert n × CanonicalHilbert n)) := by
    have : (L.graph : Set (CanonicalHilbert n × CanonicalHilbert n)) =
        (fun z : CanonicalHilbert n × CanonicalHilbert n => (T z.1, z.2)) ⁻¹'
          (A.graph : Set (CanonicalHilbert n × CanonicalHilbert n)) := by
      ext z
      simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, Set.mem_preimage]
      rw [hL]
      exact eq_comm
    rw [this]
    exact hA.preimage (by fun_prop)
  refine ⟨ContinuousLinearMap.ofIsClosedGraph hg, fun x y => ?_⟩
  rw [hL]
  rfl

theorem g62g_main {n : ℕ} (p : ClosedOperatorPolynomial n) :
    ∀ (T : CanonicalOperator n),
      (∀ x : CanonicalHilbert n, ∃ y, closedPolynomialGraph p (T x) y) →
    ∃ B : CanonicalOperator n, ∀ x y : CanonicalHilbert n,
      closedPolynomialGraph p (T x) y ↔ B x = y := by
  induction p with
  | atom A hA =>
    intro T hdom
    have hD : ∀ x, T x ∈ A.domain := by
      intro x
      obtain ⟨y, hy⟩ := hdom x
      simp only [closedPolynomialGraph, LinearPMap.mem_graph_iff] at hy
      obtain ⟨z, hz, -⟩ := hy
      rw [← hz]; exact z.2
    obtain ⟨B, hB⟩ := g62g_atom A hA T hD
    exact ⟨B, fun x y => by simp only [closedPolynomialGraph]; exact hB x y⟩
  | scalar c =>
    intro T _
    refine ⟨c • T, fun x y => ?_⟩
    simp only [closedPolynomialGraph, ContinuousLinearMap.smul_apply]
    exact eq_comm
  | add p q ihp ihq =>
    intro T hdom
    obtain ⟨Bp, hBp⟩ := ihp T (fun x => by
      obtain ⟨y, u, v, hu, hv, -⟩ := hdom x; exact ⟨u, hu⟩)
    obtain ⟨Bq, hBq⟩ := ihq T (fun x => by
      obtain ⟨y, u, v, hu, hv, -⟩ := hdom x; exact ⟨v, hv⟩)
    refine ⟨Bp + Bq, fun x y => ?_⟩
    simp only [closedPolynomialGraph, hBp, hBq, ContinuousLinearMap.add_apply]
    constructor
    · rintro ⟨u, v, rfl, rfl, rfl⟩; rfl
    · rintro rfl; exact ⟨_, _, rfl, rfl, rfl⟩
  | smul c p ihp =>
    intro T hdom
    obtain ⟨Bp, hBp⟩ := ihp T (fun x => by
      obtain ⟨y, u, hu, -⟩ := hdom x; exact ⟨u, hu⟩)
    refine ⟨c • Bp, fun x y => ?_⟩
    simp only [closedPolynomialGraph, hBp, ContinuousLinearMap.smul_apply]
    constructor
    · rintro ⟨u, rfl, rfl⟩; rfl
    · rintro rfl; exact ⟨_, rfl, rfl⟩
  | mul p q ihp ihq =>
    intro T hdom
    obtain ⟨Bq, hBq⟩ := ihq T (fun x => by
      obtain ⟨y, u, hu, -⟩ := hdom x; exact ⟨u, hu⟩)
    obtain ⟨Bp, hBp⟩ := ihp Bq (fun x => by
      obtain ⟨y, u, hu, hy⟩ := hdom x
      rw [hBq] at hu
      exact ⟨y, hu ▸ hy⟩)
    refine ⟨Bp, fun x y => ?_⟩
    simp only [closedPolynomialGraph, hBq]
    constructor
    · rintro ⟨u, rfl, h⟩; exact (hBp x y).1 h
    · intro h; exact ⟨_, rfl, (hBp x y).2 h⟩

theorem solution (n : ℕ) (hn : 0 < n) (p : ClosedOperatorPolynomial n)
    (T : CanonicalOperator n) (hdom : ∀ x : CanonicalHilbert n, ∃ y, closedPolynomialGraph p (T x) y) :
    ∃ B : CanonicalOperator n, ∀ x y : CanonicalHilbert n,
      closedPolynomialGraph p (T x) y ↔ B x = y :=
  g62g_main p T hdom
