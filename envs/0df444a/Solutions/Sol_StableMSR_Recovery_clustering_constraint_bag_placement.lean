-- Prove2me | solution 1 for StableMSR.Recovery.clustering_constraint_bag_placement
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T16:15:02.235212+00:00
-- url     : https://prove2.me/submissions/e8c72372-94dd-43be-aa63-dab5843b422c

import Definitions.Def_StableMSR_Recovery_Geometry
import Theorems.Thm_StableMSR_Recovery_clique_in_decomposition_bag

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.ScopeSubmissionAux
noncomputable def pointScope {n : ℕ} {V I : Type*} (pool : Finset I)
    (candidate : I → Cluster n) (owner : I → V) (x : Point n) : Finset V :=
  (pool.filter (fun i => x ∈ candidate i)).image owner
noncomputable def optionalScope {n : ℕ} {V I : Type*} (pool : Finset I)
    (candidate : I → Cluster n) (owner : I → V) (K : Cluster n) : Finset V :=
  K.biUnion (pointScope pool candidate owner)
lemma distance_le_diameter {n : ℕ} (d : Point n → Point n → ℝ)
    {K : Cluster n} {x y : Point n} (hx : x ∈ K) (hy : y ∈ K) : d x y ≤ diameter d K := by
  have hK : K.Nonempty := ⟨x, hx⟩
  have h₁ : d x y ≤ eccentricity d K x := by
    rw [eccentricity, dif_pos hK]
    exact Finset.le_sup' _ hy
  have h₂ : eccentricity d K x ≤ diameter d K := by
    rw [diameter, dif_pos hK]
    exact Finset.le_sup' _ hx
  exact h₁.trans h₂
end StableMSR.Recovery.ScopeSubmissionAux


set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.ClusteringScope

noncomputable def interactionGraphAt {n : ℕ} (d : Point n → Point n → ℝ)
    (R : ℝ) (N : Cluster n) : SimpleGraph N :=
  (thresholdGraph d (8 * R) N).induce (N : Set (Point n))

lemma metric_triangle {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (x y z : Point n) : d x z ≤ d x y + d y z := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  simpa only [hm] using dist_triangle x y z

lemma metric_symm {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (x y : Point n) : d x y = d y x := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  simpa only [hm] using dist_comm x y

/- The source owner rule and candidate-radius test imply the 3R member bound. -/
theorem owner_member_distance {n : ℕ} {I : Type*}
    (d : Point n → Point n → ℝ) (hd : IsMetricArray d) (R : ℝ) (N : Cluster n)
    (pool : Finset I) (candidate : I → Cluster n) (center : I → Point n) (owner : I → N)
    (howner : ∀ i ∈ pool, d (owner i) (center i) ≤ 2 * R)
    (hcandidate : ∀ i ∈ pool, ∀ x ∈ candidate i, d (center i) x ≤ R) :
    ∀ i ∈ pool, ∀ x ∈ candidate i, d (owner i) x ≤ 3 * R := by
  intro i hi x hx
  have h := metric_triangle d hd (owner i) (center i) x
  linarith [howner i hi, hcandidate i hi x hx]

/- All variables involved in one point-coverage predicate form a clique. -/
theorem point_scope_clique {n : ℕ} {I : Type*}
    (d : Point n → Point n → ℝ) (hd : IsMetricArray d) (R : ℝ) (hR : 0 ≤ R)
    (N : Cluster n) (pool : Finset I) (candidate : I → Cluster n) (owner : I → N)
    (hclose : ∀ i ∈ pool, ∀ x ∈ candidate i, d (owner i) x ≤ 3 * R) (x : Point n) :
    (ScopeSubmissionAux.pointScope pool candidate owner x : Set N).Pairwise
      (interactionGraphAt d R N).Adj := by
  classical
  letI : DecidableEq N := Classical.decEq N
  intro u hu v hv huv
  obtain ⟨i, hi, hui⟩ := Finset.mem_image.mp hu
  obtain ⟨j, hj, hvj⟩ := Finset.mem_image.mp hv
  obtain ⟨hip, hxi⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjp, hxj⟩ := Finset.mem_filter.mp hj
  have huclose : d u x ≤ 3 * R := hui ▸ hclose i hip x hxi
  have hvclose : d v x ≤ 3 * R := hvj ▸ hclose j hjp x hxj
  have hdist : d u v ≤ 8 * R := by
    have h := metric_triangle d hd u x v
    rw [metric_symm d hd x v] at h
    linarith
  exact ⟨fun h => huv (Subtype.ext h), u.property, v.property,
    hdist, (metric_symm d hd v u).le.trans hdist⟩

/- All owners of candidates meeting an optional component form a clique.
The weaker diameter bound 2R is sufficient for the source's smaller components. -/
theorem optional_scope_clique {n : ℕ} {I : Type*}
    (d : Point n → Point n → ℝ) (hd : IsMetricArray d) (R : ℝ)
    (N : Cluster n) (pool : Finset I) (candidate : I → Cluster n) (owner : I → N)
    (hclose : ∀ i ∈ pool, ∀ x ∈ candidate i, d (owner i) x ≤ 3 * R)
    (K : Cluster n) (hdiam : ∀ x ∈ K, ∀ y ∈ K, d x y ≤ 2 * R) :
    (ScopeSubmissionAux.optionalScope pool candidate owner K : Set N).Pairwise
      (interactionGraphAt d R N).Adj := by
  classical
  letI : DecidableEq N := Classical.decEq N
  intro u hu v hv huv
  obtain ⟨x, hx, hux⟩ := Finset.mem_biUnion.mp hu
  obtain ⟨y, hy, hvy⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨i, hi, hui⟩ := Finset.mem_image.mp hux
  obtain ⟨j, hj, hvj⟩ := Finset.mem_image.mp hvy
  obtain ⟨hip, hxi⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjp, hyj⟩ := Finset.mem_filter.mp hj
  have huclose : d u x ≤ 3 * R := hui ▸ hclose i hip x hxi
  have hvclose : d v y ≤ 3 * R := hvj ▸ hclose j hjp y hyj
  have hdist : d u v ≤ 8 * R := by
    have h₁ := metric_triangle d hd u x v
    have h₂ := metric_triangle d hd x y v
    rw [metric_symm d hd y v] at h₂
    linarith [hdiam x hx y hy]
  exact ⟨fun h => huv (Subtype.ext h), u.property, v.property,
    hdist, (metric_symm d hd v u).le.trans hdist⟩

/- The actual point and optional-component constraint supports each fit in one
bag of any canonical tree decomposition of the interaction graph. -/
theorem constraint_scopes_in_bags {n : ℕ} {I T : Type} [Fintype T] [DecidableEq T]
    (d : Point n → Point n → ℝ) (hd : IsMetricArray d) (R : ℝ) (hR : 0 ≤ R)
    (N : Cluster n) (pool : Finset I) (candidate : I → Cluster n) (owner : I → N)
    (hclose : ∀ i ∈ pool, ∀ x ∈ candidate i, d (owner i) x ≤ 3 * R)
    (optional : Partition n)
    (hdiam : ∀ K ∈ optional, ∀ x ∈ K, ∀ y ∈ K, d x y ≤ 2 * R)
    (tree : SimpleGraph T) (bags : T → Finset N)
    (htd : RobertsonSeymour1986.GM5.IsTreeDecomposition (interactionGraphAt d R N) tree bags) :
    (∀ x : Point n, ∃ t : T, ScopeSubmissionAux.pointScope pool candidate owner x ⊆ bags t) ∧
    (∀ K ∈ optional, ∃ t : T, ScopeSubmissionAux.optionalScope pool candidate owner K ⊆ bags t) := by
  constructor
  · intro x
    exact StableMSR.Recovery.clique_in_decomposition_bag _ tree bags htd _
      (point_scope_clique d hd R hR N pool candidate owner hclose x)
  · intro K hK
    exact StableMSR.Recovery.clique_in_decomposition_bag _ tree bags htd _
      (optional_scope_clique d hd R N pool candidate owner hclose K (hdiam K hK))

end StableMSR.Recovery.ClusteringScope
open StableMSR.Recovery

theorem solution {n : ℕ} {I T : Type}
    [Fintype T] [DecidableEq T]
    (d : Point n → Point n → ℝ) (hd : IsMetricArray d) (R : ℝ) (hR : 0 ≤ R)
    (N : Cluster n) (pool : Finset I) (candidate : I → Cluster n)
    (center : I → Point n) (owner : I → N)
    (howner : ∀ i ∈ pool, d (owner i) (center i) ≤ 2 * R)
    (hcandidate : ∀ i ∈ pool, ∀ x ∈ candidate i, d (center i) x ≤ R)
    (optional : Partition n) (hdiam : ∀ K ∈ optional, diameter d K ≤ 2 * R)
    (tree : SimpleGraph T) (bags : T → Finset N)
    (htd : RobertsonSeymour1986.GM5.IsTreeDecomposition
      ((thresholdGraph d (8 * R) N).induce (N : Set (Point n))) tree bags) :
    (∀ x : Point n, ∃ t : T, ∀ i ∈ pool, x ∈ candidate i → owner i ∈ bags t) ∧
      (∀ K ∈ optional, ∃ t : T, ∀ i ∈ pool,
        (candidate i ∩ K).Nonempty → owner i ∈ bags t) := by
  classical
  letI : DecidableEq N := Classical.decEq N
  have hclose := ClusteringScope.owner_member_distance d hd R N pool candidate center owner howner hcandidate
  have hdiam' : ∀ K ∈ optional, ∀ x ∈ K, ∀ y ∈ K, d x y ≤ 2 * R := by
    intro K hK x hx y hy
    exact (ScopeSubmissionAux.distance_le_diameter d hx hy).trans (hdiam K hK)
  obtain ⟨hp, hc⟩ := ClusteringScope.constraint_scopes_in_bags d hd R hR N pool candidate owner
    hclose optional hdiam' tree bags htd
  constructor
  · intro x
    obtain ⟨t, ht⟩ := hp x
    refine ⟨t, ?_⟩
    intro i hi hx
    exact ht (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hx⟩, rfl⟩)
  · intro K hK
    obtain ⟨t, ht⟩ := hc K hK
    refine ⟨t, ?_⟩
    intro i hi hmeet
    obtain ⟨x, hx⟩ := hmeet
    obtain ⟨hxC, hxK⟩ := Finset.mem_inter.mp hx
    exact ht (Finset.mem_biUnion.mpr ⟨x, hxK,
      Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hxC⟩, rfl⟩⟩)
