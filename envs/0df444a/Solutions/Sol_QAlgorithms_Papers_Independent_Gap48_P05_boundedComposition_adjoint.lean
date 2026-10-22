-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P05.boundedComposition_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:30:54.867054+00:00
-- url     : https://prove2.me/submissions/8c4fed60-1cc1-43c6-ad61-36a747b23195

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P05
open QAlgorithms.Papers.Independent.Gap48.P05

open Set Filter Topology

open QAlgorithms.Papers.Independent.Claimed50.P22

open QAlgorithms.Papers.Independent.Next46.P35

universe u v w z

attribute [local instance] QAlgorithms.Papers.Independent.Gap48.P05.productCharts

section g73kHelpers
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem g73k_closedGraph (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) (M : H →L[ℂ] H)
    (hM : ∀ v, M v ∈ T.domain) : ∃ S : H →L[ℂ] H, ∀ v, S v = T ⟨M v, hM v⟩ := by
  let S : H →ₗ[ℂ] H :=
    { toFun := fun v => T ⟨M v, hM v⟩
      map_add' := fun x y => by
        rw [← LinearPMap.map_add]; congr 1; ext; simp
      map_smul' := fun c x => by
        rw [RingHom.id_apply, ← LinearPMap.map_smul]; congr 1; ext; simp }
  have hgraph : (S.graph : Set (H × H)) = (fun p : H × H => (M p.1, p.2)) ⁻¹' (T.graph : Set (H × H)) := by
    ext ⟨v, w⟩
    simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, Set.mem_preimage, LinearPMap.mem_graph_iff]
    constructor
    · rintro rfl
      exact ⟨⟨M v, hM v⟩, rfl, rfl⟩
    · rintro ⟨y, hy1, hy2⟩
      rw [← hy2]
      show T y = T ⟨M v, hM v⟩
      congr 1; ext; exact hy1
  have hcl : IsClosed (S.graph : Set (H × H)) := by
    rw [hgraph]
    exact hT.preimage (by fun_prop)
  exact ⟨⟨S, S.continuous_of_isClosed_graph hcl⟩, fun v => rfl⟩

/-- core (a) -/
theorem g73k_partA (A : H →L[ℂ] H) (B : H →ₗ.[ℂ] H) (hDense : Dense (B.domain : Set H)) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ v : (A.toLinearMap.compPMap B).domain,
        ‖(A.toLinearMap.compPMap B) v‖ ≤ C * ‖(v : H)‖) ↔
      ∀ v : H, A.adjoint v ∈ B.adjoint.domain := by
  constructor
  · rintro ⟨C, hC, hb⟩ v
    rw [LinearPMap.mem_adjoint_domain_iff]
    let f : B.domain →ₗ[ℂ] ℂ := (innerₛₗ ℂ (A.adjoint v)).comp B.toFun
    show Continuous f
    refine AddMonoidHomClass.continuous_of_bound f (‖v‖ * C) fun x => ?_
    have : f x = ⟪v, A (B x)⟫_ℂ := by
      simp [f, ContinuousLinearMap.adjoint_inner_left]
    rw [this]
    calc ‖⟪v, A (B x)⟫_ℂ‖ ≤ ‖v‖ * ‖A (B x)‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * (C * ‖(x : H)‖) := by gcongr; exact hb x
      _ = ‖v‖ * C * ‖x‖ := by rw [mul_assoc]; rfl
  · intro h
    obtain ⟨S, hS⟩ := g73k_closedGraph B.adjoint (LinearPMap.adjoint_isClosed hDense) A.adjoint h
    refine ⟨‖S‖, norm_nonneg _, fun x => ?_⟩
    have key : ∀ v : H, ⟪v, A (B x)⟫_ℂ = ⟪S v, (x : H)⟫_ℂ := by
      intro v
      rw [hS v, ← ContinuousLinearMap.adjoint_inner_left]
      exact ((LinearPMap.adjoint_isFormalAdjoint hDense) ⟨A.adjoint v, h v⟩ x).symm
    set y := A (B x)
    show ‖y‖ ≤ ‖S‖ * ‖(x : H)‖
    have h1 : ‖y‖ ^ 2 ≤ ‖S‖ * ‖(x:H)‖ * ‖y‖ := by
      have := key y
      rw [inner_self_eq_norm_sq_to_K] at this
      have h2 : ‖(‖y‖ : ℂ) ^ 2‖ = ‖y‖ ^ 2 := by simp
      calc ‖y‖ ^ 2 = ‖⟪S y, (x : H)⟫_ℂ‖ := by rw [← this]; exact h2.symm
        _ ≤ ‖S y‖ * ‖(x:H)‖ := norm_inner_le_norm _ _
        _ ≤ ‖S‖ * ‖y‖ * ‖(x:H)‖ := by gcongr; exact S.le_opNorm y
        _ = _ := by ring
    rcases eq_or_lt_of_le (norm_nonneg y) with h0 | h0
    · rw [← h0]; positivity
    · nlinarith


theorem g73k_le_adj_adj (B : H →ₗ.[ℂ] H) (hD : Dense (B.domain : Set H))
    (hD2 : Dense (B.adjoint.domain : Set H)) : B ≤ B.adjoint.adjoint :=
  (LinearPMap.adjoint_isFormalAdjoint hD).le_adjoint hD2

theorem g73k_closable (B : H →ₗ.[ℂ] H) (hD : Dense (B.domain : Set H))
    (hD2 : Dense (B.adjoint.domain : Set H)) : B.IsClosable :=
  (LinearPMap.adjoint_isClosed hD2).isClosable.leIsClosable (g73k_le_adj_adj B hD hD2)

theorem g73k_closure_le (B : H →ₗ.[ℂ] H) (hD : Dense (B.domain : Set H))
    (hD2 : Dense (B.adjoint.domain : Set H)) : B.closure ≤ B.adjoint.adjoint := by
  have hc := LinearPMap.adjoint_isClosed hD2
  have h1 := hc.isClosable.closure_mono (g73k_le_adj_adj B hD hD2)
  have h2 : B.adjoint.adjoint.closure = B.adjoint.adjoint := by
    apply LinearPMap.eq_of_eq_graph
    rw [← hc.isClosable.graph_closure_eq_closure_graph]
    exact hc.submodule_topologicalClosure_eq
  rwa [h2] at h1

theorem g73k_dom_adj_adj (B : H →ₗ.[ℂ] H) (hD : Dense (B.domain : Set H))
    (hD2 : Dense (B.adjoint.domain : Set H)) (u : H) (hu : u ∈ B.adjoint.adjoint.domain) :
    u ∈ B.closure.domain := by
  set w := B.adjoint.adjoint ⟨u, hu⟩
  let e := (WithLp.linearEquiv 2 ℂ (H × H)).symm
  let K : Submodule ℂ (WithLp 2 (H × H)) := B.graph.map e.toLinearMap
  have hmem : (WithLp.toLp 2 (u, w)) ∈ Kᗮᗮ := by
    rw [Submodule.mem_orthogonal']
    intro a ha
    rw [Submodule.mem_orthogonal] at ha
    obtain ⟨a1, a2⟩ := (WithLp.ofLp a)
    have hab : ∀ x : B.domain, ⟪(x : H), (WithLp.ofLp a).1⟫_ℂ + ⟪B x, (WithLp.ofLp a).2⟫_ℂ = 0 := by
      intro x
      have := ha (WithLp.toLp 2 ((x : H), B x)) ⟨((x : H), B x), by simp, rfl⟩
      rw [WithLp.prod_inner_apply] at this
      simpa using this
    set a1 := (WithLp.ofLp a).1
    set a2 := (WithLp.ofLp a).2
    have ha2 : a2 ∈ B.adjoint.domain := by
      apply LinearPMap.mem_adjoint_domain_of_exists
      refine ⟨-a1, fun x => ?_⟩
      have := hab x
      rw [inner_neg_left, ← inner_conj_symm a2, ← inner_conj_symm a1]
      have h3 : ⟪B x, a2⟫_ℂ = -⟪(x:H), a1⟫_ℂ := by linear_combination this
      rw [h3, map_neg]
    have hBa2 : B.adjoint ⟨a2, ha2⟩ = -a1 := by
      apply LinearPMap.adjoint_apply_eq hD
      intro x
      have := hab x
      rw [inner_neg_left, ← inner_conj_symm a2, ← inner_conj_symm a1]
      have h3 : ⟪B x, a2⟫_ℂ = -⟪(x:H), a1⟫_ℂ := by linear_combination this
      rw [h3, map_neg]
    have hfa := LinearPMap.adjoint_isFormalAdjoint hD2 ⟨u, hu⟩ ⟨a2, ha2⟩
    rw [hBa2] at hfa
    rw [WithLp.prod_inner_apply]
    simp only
    change ⟪u, a1⟫_ℂ + ⟪w, a2⟫_ℂ = 0
    have : ⟪w, a2⟫_ℂ = -⟪u, a1⟫_ℂ := by rw [inner_neg_right] at hfa; exact hfa
    rw [this]; ring
  rw [Submodule.orthogonal_orthogonal_eq_closure] at hmem
  have hcl : (u, w) ∈ B.graph.topologicalClosure := by
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hmem ⊢
    have hcont : Continuous (fun z : WithLp 2 (H × H) => WithLp.ofLp z) := by fun_prop
    have := image_closure_subset_closure_image hcont ⟨_, hmem, rfl⟩
    have himg : (fun z : WithLp 2 (H × H) => WithLp.ofLp z) '' (K : Set _) = B.graph := by
      ext z
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        simpa [e] using hy
      · intro hz
        exact ⟨e z, ⟨z, hz, rfl⟩, by simp [e]⟩
    rw [himg] at this
    exact this
  rw [(g73k_closable B hD hD2).graph_closure_eq_closure_graph] at hcl
  exact LinearPMap.mem_domain_of_mem_graph hcl

end g73kHelpers

section PartialOperators

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Lemma 2.1, PDF p. 9, both clauses. The PDF has D(closure B) and
(closure B) A in (b). B need not be closed. Density is retained for B,
and separately for B* in (b), guarding Mathlib's non-dense adjoint default.
Equality of adjoints is stated with all domains explicit. -/
theorem solution
    (A : H →L[ℂ] H) (B : H →ₗ.[ℂ] H) (hDense : Dense (B.domain : Set H)) :
    (PMapBounded (A.toLinearMap.compPMap B) ↔
      ∀ v : H, A.adjoint v ∈ B.adjoint.domain) ∧
    (PMapBounded (A.toLinearMap.compPMap B) →
      ∀ v : H, ∃ h1 : v ∈ (A.toLinearMap.compPMap B).adjoint.domain,
        ∃ h2 : A.adjoint v ∈ B.adjoint.domain,
          (A.toLinearMap.compPMap B).adjoint ⟨v, h1⟩ =
            B.adjoint ⟨A.adjoint v, h2⟩) ∧
    (Dense (B.adjoint.domain : Set H) →
      (PMapBounded (A.adjoint.toLinearMap.compPMap B.adjoint) ↔
        ∀ v : H, A v ∈ B.closure.domain) ∧
      ((∀ v : H, A v ∈ B.closure.domain) →
        ∃ T : H →L[ℂ] H, ∀ v : H, ∃ hv : A v ∈ B.closure.domain,
          T v = B.closure ⟨A v, hv⟩)) := by
  have hA := g73k_partA A B hDense
  have hb : PMapBounded (A.toLinearMap.compPMap B) →
      ∀ v : H, ∃ h1 : v ∈ (A.toLinearMap.compPMap B).adjoint.domain,
        ∃ h2 : A.adjoint v ∈ B.adjoint.domain,
          (A.toLinearMap.compPMap B).adjoint ⟨v, h1⟩ =
            B.adjoint ⟨A.adjoint v, h2⟩ := by
    intro hbd v
    have h2 : A.adjoint v ∈ B.adjoint.domain := hA.1 hbd v
    have hDense' : Dense ((A.toLinearMap.compPMap B).domain : Set H) := hDense
    have key : ∀ x : (A.toLinearMap.compPMap B).domain,
        inner ℂ (B.adjoint ⟨A.adjoint v, h2⟩) (x : H) =
          inner ℂ v ((A.toLinearMap.compPMap B) x) := by
      intro x
      rw [(LinearPMap.adjoint_isFormalAdjoint hDense) ⟨A.adjoint v, h2⟩ x,
        ContinuousLinearMap.adjoint_inner_left]
      rfl
    have h1 : v ∈ (A.toLinearMap.compPMap B).adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, key⟩
    exact ⟨h1, h2, LinearPMap.adjoint_apply_eq hDense' ⟨v, h1⟩ key⟩
  refine ⟨hA, hb, fun hD2 => ?_⟩
  have hA2 := g73k_partA A.adjoint B.adjoint hD2
  rw [ContinuousLinearMap.adjoint_adjoint] at hA2
  have hle := g73k_closure_le B hDense hD2
  refine ⟨?_, ?_⟩
  · change (∃ C : ℝ, 0 ≤ C ∧ _) ↔ _
    rw [hA2]
    constructor
    · intro h v
      exact g73k_dom_adj_adj B hDense hD2 _ (h v)
    · intro h v
      exact hle.1 (h v)
  · intro h
    obtain ⟨S, hS⟩ := g73k_closedGraph B.adjoint.adjoint
      (LinearPMap.adjoint_isClosed hD2) A (fun v => hle.1 (h v))
    refine ⟨S, fun v => ⟨h v, ?_⟩⟩
    rw [hS v]
    exact (hle.2 rfl).symm

end PartialOperators

