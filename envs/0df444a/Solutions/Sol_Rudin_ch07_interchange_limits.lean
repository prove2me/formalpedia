-- Prove2me | solution 1 for Rudin.ch07_interchange_limits
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:39:24.744085+00:00
-- url     : https://prove2.me/submissions/6f9765c2-67bb-4b95-9f65-59f57e8e9203

import Mathlib
set_option autoImplicit false
open Filter Topology
theorem solution {X : Type*} [MetricSpace X] (E : Set X) (f : ℕ → X → ℂ)
    (g : X → ℂ) (A : ℕ → ℂ) (x : X) (hx : x ∈ closure (E \ {x}))
    (huc : TendstoUniformlyOn f g atTop E)
    (hA : ∀ n, Tendsto (f n) (𝓝[E \ {x}] x) (𝓝 (A n))) :
    ∃ L : ℂ, Tendsto A atTop (𝓝 L) ∧ Tendsto g (𝓝[E \ {x}] x) (𝓝 L) := by
  letI : NeBot (𝓝[E \ {x}] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hC : CauchySeq A := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp huc.uniformCauchySeqOn
      (ε / 2) (half_pos hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hle : dist (A m) (A n) ≤ ε / 2 :=
      le_of_tendsto ((hA m).dist (hA n)) (by
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact (hN m hm n hn y hy.1).le)
    exact hle.trans_lt (half_lt_self hε)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hC
  refine ⟨L, hL, ?_⟩
  have hfilter : 𝓝[E \ {x}] x ≤ 𝓟 E :=
    inf_le_right.trans (Filter.principal_mono.mpr Set.sdiff_subset)
  exact (huc.tendstoUniformlyOnFilter.mono_right hfilter).tendsto_of_eventually_tendsto
    (Filter.Eventually.of_forall hA) hL
#print axioms solution
