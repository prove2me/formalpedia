-- Prove2me | solution 1 for Rudin.ch07_arzela_ascoli
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:45:04.087356+00:00
-- url     : https://prove2.me/submissions/ac7c60ea-5d81-4f91-9a67-76dfc463165e

import Mathlib
import Definitions.Def_Rudin_ch07_families
set_option autoImplicit false
open Filter Topology Rudin
theorem solution {K : Type*} [MetricSpace K] [CompactSpace K] (f : ℕ → K → ℂ)
    (hcont : ∀ n, Continuous (f n))
    (hbdd : PointwiseBoundedOn f Set.univ) (heq : Rudin.EquicontinuousOn f Set.univ) :
    UniformlyBoundedOn f Set.univ ∧
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : K → ℂ,
      TendstoUniformlyOn (fun k => f (φ k)) g atTop Set.univ := by
  classical
  let F : ℕ → C(K, ℂ) := fun n => ⟨f n, hcont n⟩
  have he : _root_.Equicontinuous (fun g : Set.range F => (g : C(K, ℂ))) := by
    intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := heq ε hε
    refine ⟨δ, hδ, ?_⟩
    intro y hy g
    obtain ⟨n, hn⟩ := g.property
    have hh := hd n x (Set.mem_univ _) y (Set.mem_univ _) (by simpa [dist_comm] using hy)
    rw [← hn]
    simpa only [F, ContinuousMap.coe_mk, dist_eq_norm] using hh
  letI : T2Space (UniformOnFun K ℂ {s : Set K | IsCompact s}) :=
    UniformOnFun.t2Space_of_covering (by
      apply Set.eq_univ_of_forall
      intro x
      exact Set.mem_sUnion_of_mem (Set.mem_singleton x) isCompact_singleton)
  have hc : IsCompact (closure (Set.range F)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun g : C(K, ℂ) => (g : K → ℂ))
      (𝔖 := {s : Set K | IsCompact s}) (fun s hs => hs)
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · intro s hs
      exact he.equicontinuousOn s
    · intro s hs x hx
      obtain ⟨M, hM⟩ := hbdd x (Set.mem_univ _)
      refine ⟨Metric.closedBall (0 : ℂ) M, isCompact_closedBall _ _, ?_⟩
      rintro g ⟨n, rfl⟩
      simpa [F, Metric.mem_closedBall, dist_zero_right] using hM n
  obtain ⟨M, hM⟩ := hc.isBounded.exists_norm_le
  constructor
  · refine ⟨M, ?_⟩
    intro n x hx
    exact (ContinuousMap.norm_coe_le_norm (F n) x).trans
      (hM (F n) (subset_closure (Set.mem_range_self n)))
  · obtain ⟨g, hg, φ, hφ, hlim⟩ := hc.tendsto_subseq
      (fun n => subset_closure (Set.mem_range_self n))
    refine ⟨φ, hφ, (g : K → ℂ), ?_⟩
    exact (ContinuousMap.tendsto_iff_tendstoUniformly.mp hlim).tendstoUniformlyOn
#print axioms solution
