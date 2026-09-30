-- Prove2me | solution 1 for RelaxationMethod.LowDim.lemma1_case2
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:50:10.499221+00:00
-- url     : https://prove2.me/submissions/2e5a0c38-7fa2-4c77-93c8-f09ac8f19474

import Definitions.Def_RelaxationMethod_Shared_FejerMonotone
import Definitions.Def_RelaxationMethod_LowDim_AxisSphere
import Definitions.Def_RelaxationMethod_FullDim_FejerMonotone
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic
set_option autoImplicit false
open Filter
open scoped Topology

private theorem cluster_dist_eq {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (q : ℕ → EuclideanSpace ℝ (Fin n))
    (hm : ∀ a ∈ A, ∀ k, dist (q (k+1)) a ≤ dist (q k) a)
    (x y : EuclideanSpace ℝ (Fin n)) (hx : MapClusterPt x atTop q)
    (hy : MapClusterPt y atTop q) :
    ∀ a ∈ affineSpan ℝ A, dist x a = dist y a := by
  have he (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ A) : dist x a = dist y a := by
    have hm' : Antitone (fun k => dist (q k) a) := antitone_nat_of_succ_le (hm a ha)
    have hb : BddBelow (Set.range (fun k => dist (q k) a)) := ⟨0,by rintro _ ⟨k,rfl⟩; exact dist_nonneg⟩
    have ht := tendsto_atTop_ciInf hm' hb
    obtain ⟨u,hu,hux⟩ := hx.tendsto_subseq
    obtain ⟨v,hv,hvy⟩ := hy.tendsto_subseq
    have hxd : Tendsto (fun k => dist (q (u k)) a) atTop (𝓝 (dist x a)) :=
      hux.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a))
    have hyd : Tendsto (fun k => dist (q (v k)) a) atTop (𝓝 (dist y a)) :=
      hvy.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a))
    exact (tendsto_nhds_unique hxd (ht.comp hu.tendsto_atTop)).trans
      (tendsto_nhds_unique hyd (ht.comp hv.tendsto_atTop)).symm
  have hsub : affineSpan ℝ A ≤ AffineSubspace.perpBisector x y :=
    affineSpan_le.mpr (fun a ha => AffineSubspace.mem_perpBisector_iff_dist_eq'.mpr (he a ha))
  intro a ha
  exact AffineSubspace.mem_perpBisector_iff_dist_eq'.mp (hsub ha)

private theorem fejer_bounded {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (q : ℕ → EuclideanSpace ℝ (Fin n))
    (hm : ∀ a ∈ A, ∀ k, dist (q (k+1)) a ≤ dist (q k) a)
    (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ A) :
    ∀ k, q k ∈ Metric.closedBall a (dist (q 0) a) := by
  intro k
  have ht : Antitone (fun k => dist (q k) a) := antitone_nat_of_succ_le (hm a ha)
  exact ht (Nat.zero_le k)

open RelaxationMethod.LowDim

theorem solution {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) (hA : A.Nonempty)
    (hr : affineSpan ℝ A ≠ ⊤) (q : ℕ → EuclideanSpace ℝ (Fin n))
    (hq : RelaxationMethod.Shared.IsFejerMonotone A q) :
    (∃ l, Tendsto q atTop (𝓝 l)) ∨
      ∃ c ∉ affineSpan ℝ A,
        ∀ x, MapClusterPt x atTop q → x ∈ axisSphere (affineSpan ℝ A) c := by
  classical
  by_cases hconv : ∃ l, Tendsto q atTop (𝓝 l)
  · exact Or.inl hconv
  apply Or.inr
  obtain ⟨a,ha⟩ := hA
  have hb := fejer_bounded A q hq.2.2 a ha
  have hc := isCompact_closedBall a (dist (q 0) a)
  obtain ⟨c,hcball,hcc⟩ := hc.exists_mapClusterPt (f := atTop) (u := q) (Filter.le_principal_iff.mpr (Filter.mem_map.mpr (Filter.Eventually.of_forall hb)))
  have hcout : c ∉ affineSpan ℝ A := by
    intro hcin
    apply hconv
    refine ⟨c,hc.tendsto_nhds_of_unique_mapClusterPt (Filter.Eventually.of_forall hb) ?_⟩
    intro x hx hxc
    have he := cluster_dist_eq A q hq.2.2 x c hxc hcc c hcin
    simpa using he
  refine ⟨c,hcout,?_⟩
  intro x hx
  exact cluster_dist_eq A q hq.2.2 x c hx hcc
